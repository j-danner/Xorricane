#include "solve.hpp"

#include "argparse/argparse.hpp"


//main -- parses args
int main(int argc, char const *argv[])
{
    auto begin = std::chrono::steady_clock::now();

    argparse::ArgumentParser program(__PROJECT_NAME, __VERSION__, argparse::default_arguments::help);
    program.add_argument("-v", "--version")
      .action([=]([[maybe_unused]] const std::string& s) {
        std::stringstream out;
        out << "c " << __PROJECT_NAME << " created by J. Danner (2023)" << std::endl;
        out << "c version:           " << __PROJECT_VERSION << std::endl;
        out << "c compilation date:  " << __DATE__ << " at " << __TIME__ << std::endl;
        out << "c compiler:          " << __CMAKE_CXX_COMPILER_ID << " " << __CMAKE_CXX_COMPILER_VERSION << " using C++" << __CMAKE_CXX_STANDARD << std::endl;
        out << "c compilation flags:" << __CMAKE_CXX_FLAGS << std::endl;
      #ifdef USING_JEMALLOC
        out << "c using jemalloc for memory allocation" << std::endl;
      #endif
        std::cout << out.str();
        std::exit(0);
      })
      .default_value(false)
      .help("shows version and compilation information")
      .implicit_value(true)
      .nargs(0);
    
    //add args:
    //fname
    program.add_argument("fname")
        .help("path to 2xnf-instance");

    //dec_heu
    program.add_argument("-dh","--decision-heuristic")
        .help("decision heuristic; 'vsids', 'lwl' -- longest watch_list, 'lex' -- lexicographically first, 'swl'")
        .default_value(std::string("vsids"))
        .action([](const std::string& value) {
            static const vec<std::string> choices = { "vsids", "lwl", "lex", "swl" };
            if (std::find(choices.begin(), choices.end(), value) != choices.end()) {
                return value;
            }
            //arg invalid!
            throw std::runtime_error("invalid argument passed for parameter -dh");
        });
    
    //phase_opt
    program.add_argument("-po","--phase-options")
        .help("phase options; 'save', 'save_inv', 'rand'")
        .default_value(std::string("save"))
        .action([](const std::string& value) {
            static const vec<std::string> choices = { "save", "save_inv", "rand" };
            if (std::find(choices.begin(), choices.end(), value) != choices.end()) {
                return value;
            }
            //arg invalid!
            throw std::runtime_error("invalid argument passed for parameter -po");
        });


    //fls opts
    //program.add_argument("-fls","--failed-lit-search")
    //    .help("failed literal search; 'no' to deactivate, 'trivial' to only search for trivial, and 'full' to search for all failed literals.")
    //    .default_value(std::string("no"))
    //    .action([](const std::string& value) {
    //        static const vec<std::string> choices = { "no", "trivial", "full" };
    //        if (std::find(choices.begin(), choices.end(), value) != choices.end()) {
    //            return value;
    //        }
    //        //arg invalid!
    //        throw std::runtime_error("invalid argument passed for parameter -fls");
    //    });
    
    //upd opts
    //program.add_argument("-upd","--update-alg")
    //    .help("algorithm to use for update-graph function, 'ts' for alg in two steps (1. update all xlits, 2. merge verts); 'hf' for hash-fight based update; 'par' for parallel version.")
    //    .default_value(std::string("ts"))
    //    .action([](const std::string& value) {
    //        static const vec<std::string> choices = { "ts", "hf", "par", "hfd" };
    //        if (std::find(choices.begin(), choices.end(), value) != choices.end()) {
    //            return value;
    //        }
    //        //arg invalid!
    //        throw std::runtime_error("invalid argument passed for parameter -upd");
    //    });
    
    //cdcd opts
    program.add_argument("-ca","--conflict-analysis")
        .help("algorithm to use for conflict analysis, 'no' (means DPLL-solving), 'dpll' (means cdcl-implementation with DPLL-like learning (USE ONLY FOR DEBUGGING!)) or '1uip'")
        .default_value(std::string("1uip"))
        .action([](const std::string& value) {
            static const vec<std::string> choices = { "no", "dpll", "1uip" };
            if (std::find(choices.begin(), choices.end(), value) != choices.end()) {
                return value;
            }
            //arg invalid!
            throw std::runtime_error("invalid argument passed for parameter -ca");
        });
    
    //jobs
    //program.add_argument("-j","--jobs")
    //    .help("parallel jobs (threads) to use (must NOT be larger than actual number of available threads!)")
    //    .default_value(1)
    //    .scan<'i', int>();
        
    //verbosity
    #ifdef VERBOSITY
        program.add_argument("-vb", "--verb")
            .help("verbosity (choose in 0-100)")
            .default_value(0)
            .scan<'i', int>();
    #endif
    
    //timeout
    program.add_argument("-t","--time-out")
        .help("timeout in seconds (negative to deactivate)")
        .default_value(-1)
        .scan<'i', int>();

    try {
        program.parse_args(argc, argv);
    } catch (const std::runtime_error& err) {
        std::cerr << err.what() << std::endl;
        std::cerr << program;
        std::exit(1);
    }

    //parse string-input to 
    auto fname = program.get<std::string>("fname");

    auto dh_str = program.get<std::string>("-dh");
    dec_heu dh = dec_heu::lwl;
    if(dh_str=="vsids") dh = dec_heu::vsids;
    else if(dh_str=="lwl") dh = dec_heu::lwl;
    else if(dh_str=="swl") dh = dec_heu::swl;
    else if(dh_str=="lex") dh = dec_heu::lex;
    
    auto po_str = program.get<std::string>("-po");
    phase_opt po = phase_opt::save;
    if(po_str=="rand") po = phase_opt::rand;
    else if(po_str=="save") po = phase_opt::save;
    else if(po_str=="save_inv") po = phase_opt::save_inv;
    
    auto ca_str = program.get<std::string>("-ca");
    ca_alg ca = ca_alg::fuip;
    if(ca_str=="no") ca = ca_alg::no;
    else if(ca_str=="dpll") ca = ca_alg::dpll;
    else if(ca_str=="1uip") ca = ca_alg::fuip;

    //auto jobs = program.get<int>("-j");
    auto jobs = 1;
    
    #ifdef VERBOSITY
        int verb = program.get<int>("-vb");
    #else
        int verb = 0;
    #endif
    
    auto time_out = program.get<int>("-t");

    //parse file
    try {
        parsed_xnf p_xnf = parse_file( fname );

        //set upt options
        options opts( p_xnf.num_vars, p_xnf.num_cls, dh, po, ca, jobs, verb, time_out );

        stats s = solve(p_xnf.cls, opts);
        s.begin = begin;

        if(s.finished && s.sat) { //check sol!
            if(check_sol(p_xnf.cls, s.sol)) {
                std::cout << "c solution verified" << std::endl;
                return 0;
            } else {
                std::cout << "c solution INCORRECT!" << std::endl;
                return 1; //
            }
        } else {
            return 0;
        }
    } catch (std::exception &ex) {
        std::cout << "s INDEFINITE" << std::endl;
        return 1;
    }
}