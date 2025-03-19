#include <unistd.h>

#include "misc.hpp"
#include "io.hpp"

#include "argparse/argparse.hpp"


//main -- parses args
int main(int argc, char const *argv[])
{
    stats s;
    s.begin  = std::chrono::high_resolution_clock::now();

    argparse::ArgumentParser program(__PROJECT_NAME, __VERSION__, argparse::default_arguments::help);

    program.set_usage_max_line_width(120);
    
    program.add_description("Conflict driven SAT solver for XOR-OR-AND normal forms.");

    program.add_argument("-v", "--version")
      .action([=]([[maybe_unused]] const std::string& s) {
        std::stringstream out;
        out << "c " << __PROJECT_NAME << " created by J. Danner (2023-25)" << std::endl;
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
        .help("timeout in seconds")
        .default_value(-1)
        .scan<'i', int>()
        .nargs(1);

    program.add_usage_newline();
    
    //add args:
    //fname
    if(isatty(STDIN_FILENO)) {
        program.add_argument("fname")
            .help("path to XNF instance")
            .nargs(1);
    }

    //dec_heu
    program.add_argument("-dh","--decision-heuristic")
        .help("decision heuristic; 'vsids', 'lwl' (longest watch list), 'swl' (shortest watch list), or 'lex' (lexicographical)")
        .default_value(std::string("vsids"))
        .choices("vsids", "lwl", "swl", "lex")
        .nargs(1);
    
    //guessing path input
    program.add_argument("-gp","--guessing-path")
        .help("path to file with guessing path, where each line contains exactly one literal corresponding to the variable assignment to be guessed next; lines are skipped if variables already assigned")
        .nargs(1);
        //undocumented: if var name is negative we first guess the ind to be false instead of true
    
    
    //phase_opt
    program.add_argument("-po","--phase-options")
        .help("phase saving options; 'save', 'save_inv', 'rand'")
        .default_value(std::string("save"))
        .choices("save", "save_inv", "rand")
        .nargs(1);


    //cdcl opts
    program.add_argument("-ca","--conflict-analysis")
        .help("conflict analysis; 'no' (DPLL) or '1uip' (1UIP/TRLearning)")
        .default_value(std::string("1uip"))
        .choices("no", "dpll", "1uip", "1uip+")
        .nargs(1);

    //clause minimization
    program.add_argument("-cm","--clause-minimization")
        .help("activate (experimental!) clause minimization")
        .flag();
    
    
    //restart opts
    program.add_argument("-rh","--restart-heuristic")
        .help("restart schedule; 'no' (never), 'fixed' (after fixed number of conflicts), 'luby' (theoretical optimal), 'lbd' (dynamic lbd-based restarts)")
        .default_value(std::string("lbd"))
        .choices("no", "fixed", "luby", "lbd")
        .nargs(1);
    
    //deletion opts
    program.add_argument("-delh","--deletion-heuristic")
        .help("deletion heuristic for move/delete in each tier; 'avg_util' (average util), 'util' (median utility), 'lbd' (median LBD)")
        .default_value(std::string("avg_util"))
        .choices("avg_util", "util", "lbd")
        .nargs(1);

    //linalg-in-processing options
    auto& arg_ge = program.add_argument("-ge","--gauss-elim")
        .help("gauss-elim in-processing after every i-th decision")
        .default_value(0)
        .scan<'i', int>()
        .nargs(1);
    program.add_hidden_alias_for(arg_ge, "-la"); //old flag
    
    //lazy gauss-elim
    auto& arg_lgj= program.add_argument("-no-lgj","--no-lazy-gauss-jordan-elim")
        .help("deactivate lazy gauss-jordan-elim of unit clauses")
        .flag();
    program.add_hidden_alias_for(arg_lgj, "-no-lge"); //old flag
    

    //initial reduction opts
    program.add_argument("-ip","--initial-propagation")
        .help("initial propagation of non-forcing linerals; 'no' (no), 'nbu' (reduce if each linerals size does not blow up), or 'full' (full reduction)")
        .default_value(std::string("no"))
        .choices("no", "nbu", "full")
        .nargs(1);
    
    //preproc (SCC+FLS)
    program.add_argument("-pp","--preprocess")
        .help("preprocessing via implication graphs (see 2-Xornado); 'no' (no), 'scc' (strongly connected components), or 'scc_fls' (strongly connected components and failed linerals)")
        .default_value(std::string("scc_fls"))
        .choices("no", "scc", "scc_fls")
        .nargs(1);
    
    
    
    //equiv opts
    program.add_argument("-no-eq","--no-equiv-sub")
        .help("deactivate substitution of equivalence linerals")
        .flag();
    
    
    //max sols to compute
    program.add_argument("-ms", "--maxsol")
        .help("number of solutions to compute; -1 to compute all solutions")
        .default_value(1)
        .scan<'i', int>()
        .nargs(1);
    

    //gcp-out
    program.add_argument("-g","--gcp-out")
        .help("applies GCP once and outputs result")
        .default_value(std::string("out.xnf"))
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
    
    bool lgj = !program.is_used("-no-lgj");
    
    auto rh_str = program.get<std::string>("-rh");
    restart_opt rh = restart_opt::luby;
    if(rh_str=="no") rh = restart_opt::no;
    else if(rh_str=="fixed") rh = restart_opt::fixed;
    else if(rh_str=="luby") rh = restart_opt::luby;
    else if(rh_str=="lbd") rh = restart_opt::lbd;
    
    auto delh_str = program.get<std::string>("-delh");
    deletion_opt delh = deletion_opt::avg_util;
    if(delh_str=="avg_util") delh = deletion_opt::avg_util;
    else if(delh_str=="util") delh = deletion_opt::util;
    else if(delh_str=="lbd") delh = deletion_opt::lbd;
    
    auto ip_str = program.get<std::string>("-ip");
    initial_prop_opt ip = initial_prop_opt::no;
    if(ip_str=="no") ip = initial_prop_opt::no;
    else if(ip_str=="nbu") ip = initial_prop_opt::nbu;
    else if(ip_str=="full") ip = initial_prop_opt::full;
    
    auto pp_str = program.get<std::string>("-pp");
    xornado_preproc pp = xornado_preproc::scc_fls;
    if(pp_str=="no") pp = xornado_preproc::no;
    else if(pp_str=="scc") pp = xornado_preproc::scc;
    else if(pp_str=="scc_fls") pp = xornado_preproc::scc_fls;
    
    bool eq = !program.is_used("-no-eq");

    const bool only_gcp = program.is_used("-g");
    const std::string gcp_out = only_gcp ? program.get<std::string>("-g") : "";
    
    const std::string gp_fname = program.is_used("-gp") ? program.get<std::string>("-gp") : "";
    if(program.is_used("-gp")) dh = dec_heu::lex;
    
    #ifdef VERBOSITY
        const int verb = program.get<int>("-vb");
    #else
        int verb = 1;
    #endif
        
    const auto time_out = program.get<int>("-t");
    
    const int sol_count = program.get<int>("-ms");
    
    auto gauss_elim_schedule = program.get<int>("-ge");

    //parse file
    try {
        guessing_path P = parse_gp( gp_fname );
        auto p_xnf = parse_file( fname );
        assert( P.assert_data_struct() );

        //set upt options
        options opts( dh, po, ca, cm, rh, ip, pp, eq, lgj, gauss_elim_schedule, verb, time_out, sol_count, P );
        //TODO: clean up construction of options: load defaults at start of parsing and gradually fix the choices!
        opts.del = delh;

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
        std::cout << "c [EXCEPTION] " << ex.what() << std::endl;
        std::cout << "s INDEFINITE" << std::endl;
        return 1;
    }
}