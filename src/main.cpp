#include <unistd.h>

#include "misc.hpp"
#include "io.hpp"

#include "argparse/argparse.hpp"


//main -- parses args
int main(int argc, char const *argv[])
{
    stats s;
    s.begin  = std::chrono::steady_clock::now();

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
    if(isatty(STDIN_FILENO)) {
        program.add_argument("fname")
            .help("path to 2xnf-instance")
            .nargs(1);
    }

    //dec_heu
    program.add_argument("-dh","--decision-heuristic")
        .help("decision heuristic; 'vsids', 'lwl' (longest watch list), 'swl' (shortest watch list), or 'lex' (lexicographical)")
        .default_value(std::string("vsids"))
        .action([](const std::string& value) {
            static const vec<std::string> choices = { "vsids", "lwl", "lex", "swl" };
            if (std::find(choices.begin(), choices.end(), value) != choices.end()) {
                return value;
            }
            //arg invalid!
            throw std::runtime_error("invalid argument passed for parameter -dh");
        }).nargs(1);
    
    //phase_opt
    program.add_argument("-po","--phase-options")
        .help("phase saving options; 'save', 'save_inv', 'rand'")
        .default_value(std::string("save"))
        .action([](const std::string& value) {
            static const vec<std::string> choices = { "save", "save_inv", "rand" };
            if (std::find(choices.begin(), choices.end(), value) != choices.end()) {
                return value;
            }
            //arg invalid!
            throw std::runtime_error("invalid argument passed for parameter -po");
        }).nargs(1);


    //cdcl opts
    program.add_argument("-ca","--conflict-analysis")
        .help("algorithm to use for conflict analysis; 'no' (DPLL) or '1uip' (1UIP)")
        .default_value(std::string("1uip"))
        .action([](const std::string& value) {
            static const vec<std::string> choices = { "no", "dpll", "1uip", "1uip+" };
            if (std::find(choices.begin(), choices.end(), value) != choices.end()) {
                return value;
            }
            //arg invalid!
            throw std::runtime_error("invalid argument passed for parameter -ca");
        }).nargs(1);

    //clause minimization
    program.add_argument("-cm","--clause-minimization")
        .help("activate heuristic clause minimization")
        .flag();
    
    
    //restart opts
    program.add_argument("-rh","--restart-heuristic")
        .help("heuristic to schedule restarts; 'no' (never), 'fixed' (after fixed number of conflicts) or 'luby' (theoritcal optimal)")
        .default_value(std::string("luby"))
        .action([](const std::string& value) {
            static const vec<std::string> choices = { "no", "fixed", "luby" };
            if (std::find(choices.begin(), choices.end(), value) != choices.end()) {
                return value;
            }
            //arg invalid!
            throw std::runtime_error("invalid argument passed for parameter -rh");
        }).nargs(1);
    
    //initial reduction opts
    program.add_argument("-ip","--initial-propagation")
        .help("initial propagation heuristic of non-forcing linerals; 'no' (no), 'nbu' (reduce if lineral's size does not blow up), or 'full' (full reduction)")
        .default_value(std::string("no"))
        .action([](const std::string& value) {
            static const vec<std::string> choices = { "no", "nbu", "full" };
            if (std::find(choices.begin(), choices.end(), value) != choices.end()) {
                return value;
            }
            //arg invalid!
            throw std::runtime_error("invalid argument passed for parameter -ip");
        }).nargs(1);
    
    
    //equiv opts
    program.add_argument("-no-eq","--no-equiv-lit")
        .help("deactivate tracking and usage of equivalent literals")
        .flag();
    
    
    //verbosity
    #ifdef VERBOSITY
        program.add_argument("-vb", "--verb")
            .help("verbosity level (choose in 0-100)")
            .default_value(1)
            .scan<'i', int>()
            .nargs(1);
    #endif
    
    //timeout
    program.add_argument("-t","--time-out")
        .help("timeout in seconds (negative to deactivate)")
        .default_value(-1)
        .scan<'i', int>()
        .nargs(1);

    //gcp-out
    program.add_argument("-g","--gcp-out")
        .help("applies GCP once and outputs result")
        .default_value(std::string("out.xnf"))
        .nargs(1);
    
    //guessing path input
    program.add_argument("-gp","--guessing-path")
        .help("path to file storing guessing path; each line contains exactly one number corr to the corresponding variable")
        .nargs(1);
        //undocumented: if var name is negative we first guess the ind to be false instead of true


    //max sols to compute
    program.add_argument("-ms", "--maxsol")
        .help("number of solutions to compute; -1 to compute all solutions")
        .default_value(1)
        .scan<'i', int>()
        .nargs(1);
    
    //linalg-in-processing options
    program.add_argument("-la","--lin-alg")
        .help("schedule linear algebra in-processing after every i-th decision")
        .default_value(0)
        .scan<'i', int>()
        .nargs(1);

    try {
        program.parse_args(argc, argv);
    } catch (const std::runtime_error& err) {
        std::cerr << err.what() << std::endl;
        std::cerr << program;
        std::exit(1);
    }

    //parse string-input to 
    auto fname = isatty(STDIN_FILENO) ? program.get<std::string>("fname") : " ";

    auto dh_str = program.get<std::string>("-dh");
    dec_heu dh = dec_heu::vsids;
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
    else if(ca_str=="1uip+") ca = ca_alg::fuip_opt;
    
    bool cm = program.is_used("-cm");
    
    auto rh_str = program.get<std::string>("-rh");
    restart_opt rh = restart_opt::luby;
    if(rh_str=="no") rh = restart_opt::no;
    else if(rh_str=="fixed") rh = restart_opt::fixed;
    else if(rh_str=="luby") rh = restart_opt::luby;
    
    auto ip_str = program.get<std::string>("-ip");
    initial_prop_opt ip = initial_prop_opt::no;
    if(ip_str=="no") ip = initial_prop_opt::no;
    else if(ip_str=="nbu") ip = initial_prop_opt::nbu;
    else if(ip_str=="full") ip = initial_prop_opt::full;
    
    bool eq = !program.is_used("-no-eq");

    const bool only_gcp = program.is_used("-g");
    const std::string gcp_out = only_gcp ? program.get<std::string>("-g") : "";
    
    const std::string gp_fname = program.is_used("-gp") ? program.get<std::string>("-gp") : "";
    if(program.is_used("-gp")) dh = dec_heu::lex;

    //auto jobs = program.get<int>("-j");
    const auto jobs = 1;
    
    #ifdef VERBOSITY
        const int verb = program.get<int>("-vb");
    #else
        int verb = 1;
    #endif
        
    const auto time_out = program.get<int>("-t");
    
    const int sol_count = program.get<int>("-ms");
    
    auto lin_alg_schedule = program.get<int>("-la");

    //parse file
    try {
        guessing_path P = parse_gp( gp_fname );
        auto p_xnf = parse_file( fname );
        assert( P.assert_data_struct() );

        //set upt options
        options opts( dh, po, ca, cm, rh, ip, eq, lin_alg_schedule, jobs, verb, time_out, sol_count, P );

        if(only_gcp) {
            stats s;
            std::string out = gcp_only(p_xnf.cls, p_xnf.num_vars, opts, s);
            if(out.size()>0) {
                write_str(gcp_out, out);
                return 0;
            }
            return 1; //gcp failed.
        }

        return solve(p_xnf.cls, p_xnf.num_vars, opts, s);
    } catch (std::exception &ex) {
        std::cout << "s INDEFINITE" << std::endl;
        return 1;
    }
}