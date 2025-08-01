//file to test implementation of solve
#include "../src/solver.hpp"
#include "../src/io.hpp"
#include "../src/misc.cpp"

#include <catch2/catch_all.hpp>

const auto xnf_path = std::string(BENCH_FILES);

TEST_CASE( "solving 2xnf test instances" , "[solver]" ) {
  #ifndef NDEBUG
    int la_sch = GENERATE(0,1,5);
    dec_heu dh = GENERATE(dec_heu::vsids, dec_heu::lex);
    phase_opt po = phase_opt::save;
    ca_alg ca = GENERATE(ca_alg::no, ca_alg::fuip);
    initial_prop_opt ip = GENERATE(initial_prop_opt::no, initial_prop_opt::nbu, initial_prop_opt::full);
    xornado_preproc pp = xornado_preproc::no;
    bool lgj = true;
    bool cm = GENERATE(true, false);
    bool equiv = true;
    int verb = 0;
    restart_opt rh = restart_opt::luby;
  #else
    int la_sch = GENERATE(0,1,5,10);
    dec_heu dh = GENERATE(dec_heu::vsids, dec_heu::lwl, dec_heu::swl, dec_heu::lex);
    phase_opt po = GENERATE(phase_opt::rand, phase_opt::save, phase_opt::save_inv);
    ca_alg ca = GENERATE(ca_alg::dpll, ca_alg::no, ca_alg::fuip);
    initial_prop_opt ip = GENERATE(initial_prop_opt::no, initial_prop_opt::nbu, initial_prop_opt::full);
    bool equiv = GENERATE(true, false);
    bool cm = GENERATE(true, false);
    bool lgj = GENERATE(true, false);
    xornado_preproc pp = GENERATE(xornado_preproc::no, xornado_preproc::scc);
    int verb = 0;
    restart_opt rh = restart_opt::luby;
  #endif

    guessing_path P; 
    options opt(dh, po, ca, cm, rh, ip, pp, equiv, lgj, la_sch, verb, -1, 1, P);

    SECTION( "test1.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test1.xnf");
        auto slvr = solver(clss, opt);
    
        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT
        //CHECK( s.sol == vec<bool>({false,false,false}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test2.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test2.xnf");
        auto slvr = solver(clss, opt);
        CHECK( slvr.to_str() == "x1 x3+1; x1+1 x2+x3; x2 x3+1; x2+1 x1+x3;" );
        //CHECK( slvr.to_str() == "x1 x3+1; x1+1 x2+x3; x1+x3 x2+1; x2 x3+1;" );
    
        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT
        //CHECK( s.sol == vec<bool>({false,false,false}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test3.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test3.xnf");
        auto slvr = solver(clss, opt);
        //CHECK( ((ip!=initial_prop_opt::no) || (slvr.to_str() == "x1+x2+1; x1+x5; x2+x3+1; x3+x4+1; x4+x5;")) );
    
        stats s = slvr.solve();
        CHECK( s.is_sat() == false ); //UNSAT
    }
    
    SECTION( "test18.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test18.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test5.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test5.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        //CHECK( s.sol == vec<bool>({false,false,false,false,false}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test6.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test6.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        //CHECK( s.sol == vec<bool>({false,false}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test6_.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test6_.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( s.sols.back() == vec<bool>({false,true}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test7.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test7.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        //CHECK( s.sol == vec<bool>({true,false,false,true,true}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test8.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test8.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        //CHECK( s.sol == vec<bool>({true,true,true}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test9.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test9.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        //CHECK( s.sol == vec<bool>({true,false,true,false,false}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test10.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test10.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        //CHECK( s.sol == vec<bool>({true,true,false,false}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test11.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test11.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        //CHECK( s.sol == vec<bool>({false}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test12.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test12.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test13.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test13.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test14.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test14.xnf");
        auto slvr = solver(clss, opt);
        //CHECK( slvr.to_str() == "x2 x1+x2; x2+1 x1+x2+1;0" );
        //CHECK( slvr.to_str() == "x2 x1+x2; x2+1 x1+x2+1;" );
        //CHECK( slvr.to_str() == "x2 x1+x2; x2+1 x1+1;" );

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test15.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test15.xnf");
        auto slvr = solver(clss, opt);
        //CHECK( slvr.to_str() == "x1+x2 x1+1; x2+1 x1+x2+1;x2+1" );
        //CHECK( slvr.to_str() == "x1+x2 x1+1; x2+1 x1+x2+1;" );
        //CHECK( slvr.to_str() == "x1+1 x2; x2+1 x1+1;" );

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test16.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test16.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test17.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test17.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test4.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test4.xnf");
        auto slvr = solver(clss, opt);
        CHECK( slvr.to_str() == "x1 x2+1; x2 x3+1; x3 x4+1; x3+x5 x6; x4 x5+x6+1; x5+x6 x1+1; x6+1 x7+1; x7 x3+x5+1;" );
        //CHECK( slvr.to_str() == "x1 x2+1; x1+1 x5+x6; x2 x3+1; x3 x4+1; x3+x5 x6; x3+x5+1 x7; x4 x5+x6+1; x6+1 x7+1;" );
        
        stats s = slvr.solve();
        CHECK( s.is_sat() == false ); //UNSAT!
    }
    
    SECTION( "test19.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test19.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test20.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test20.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test21.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test21.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test22_.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test22_.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test22.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test22.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test23.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test23.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test24.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test24.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test25.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test25.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test26.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test26.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test27.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test27.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test28.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test28.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test29.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test29.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test30.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test30.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test31.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test31.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "rand-3-6.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/rand/rand-3-6.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( xnf_path + "/2xnfs/cdcl/tmpzw1cx_np.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/cdcl/tmpzw1cx_np.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test32.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test32.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test36.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test36.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test37.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test37.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test38.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test38.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test39.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test39.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test43.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test43.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == false );
    }
    
    SECTION( "test44.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test44.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test45.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test45.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test47.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test47.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test48.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test48.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test49.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test49.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test50.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test50.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test51.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test51.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test52.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test52.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test53.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test53.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test54.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test54.xnf");
        auto slvr = solver(clss, opt);
        //slvr.get_opts()->verb = 120;

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test35.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test35.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test69.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test69.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == false ); //UNSAT!
    }
    
    SECTION( "test70.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test70.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test72.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test72.xnf"); //only one empty clause
        CHECK(clss.num_cls==1);
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == false ); //UNSAT!
    }
}

TEST_CASE( "solving 2xnf test instances with gp" , "[solver][gp]" ) {
    SECTION( "flat30-100.xnf" ) {
        guessing_path P;
        P.insert(2, bool3::True);
        P.insert(1);
        P.insert(10);
        P.insert(11);
        P.insert(83);
        P.insert(74);
        CHECK( P.assert_data_struct() );
        //auto P = parse_gp("gp");
        auto clss_gp = parse_file(xnf_path + "/2xnfs/flat30-100.xnf");
        auto slvr_gp = solver(clss_gp, P);
        auto clss = parse_file(xnf_path + "/2xnfs/flat30-100.xnf");
        auto slvr = solver(clss);

        stats s_gp = slvr_gp.solve();
        stats s = slvr.solve();

        CHECK( s.is_sat() == true ); //SAT!
        CHECK( s_gp.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
        CHECK( check_sols(clss_gp.cls, s_gp.sols) );

        CHECK( s.sols.front() != s_gp.sols.front() );
        CHECK( check_sols(clss.cls, s_gp.sols) );
    }
    
    SECTION( "test10.xnf" ) {
        guessing_path P;
        P.insert(1, bool3::True);
        CHECK( P.assert_data_struct() );
        //auto P = parse_gp("gp");
        auto clss_gp = parse_file(xnf_path + "/2xnfs/test10.xnf");
        auto slvr_gp = solver(clss_gp, P);
        auto clss = parse_file(xnf_path + "/2xnfs/test10.xnf");
        auto slvr = solver(clss);

        stats s_gp = slvr_gp.solve();
        stats s = slvr.solve();

        CHECK( s.is_sat() == true ); //SAT!
        CHECK( s_gp.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
        CHECK( check_sols(clss_gp.cls, s_gp.sols) );

        //check that after guessing_path sol of s_gp, we get a sol of original clss
        CHECK( s.sols.front() != s_gp.sols.front() );
    }
    
    SECTION( "eno_s4_mixed_quad.xnf" ) {
        guessing_path P;
        P.insert(1, bool3::False);
        P.insert(2, bool3::True);
        P.insert(3, bool3::False);
        P.insert(4, bool3::True);
        CHECK( P.assert_data_struct() );
        //auto P = parse_gp("gp");
        auto clss_gp = parse_file(xnf_path + "/2xnfs/enocoro_s4_mixed_quad.xnf");
        auto slvr_gp = solver(clss_gp, P);

        stats s_gp = slvr_gp.solve();

        CHECK( s_gp.is_sat() == true ); //SAT!
        CHECK( check_sols(clss_gp.cls, s_gp.sols) );

        //check that after guessing_path sol of s_gp, we get a sol of original clss
        CHECK( s_gp.sols.front() == vec<bool>({false, true, false, true, true, true, true, false}) );
    }
    
    SECTION( "eno_s4_mixed_quad.xnf" ) {
        guessing_path P;
        P.insert(5, bool3::False);
        P.insert(6, bool3::True);
        P.insert(7, bool3::False);
        P.insert(8, bool3::True);
        CHECK( P.assert_data_struct() );
        //auto P = parse_gp("gp");
        auto clss_gp = parse_file(xnf_path + "/2xnfs/enocoro_s4_mixed_quad.xnf");
        auto slvr_gp = solver(clss_gp, P);

        stats s_gp = slvr_gp.solve();

        CHECK( s_gp.is_sat() == true ); //SAT!
        CHECK( check_sols(clss_gp.cls, s_gp.sols) );

        //check that after guessing_path sol of s_gp, we get a sol of original clss
        CHECK( s_gp.sols.front() == vec<bool>({false, true, false, false, false, true, false, true}) );
    }
}

TEST_CASE( "solving xnf test instances" , "[solver]" ) {
    SECTION( "test1.xnf" ) {
        auto clss = parse_file(xnf_path + "/xnfs/test1.xnf");
        auto slvr = solver(clss);
    
        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test2.xnf" ) {
        auto clss = parse_file(xnf_path + "/xnfs/test2.xnf");
        auto slvr = solver(clss);
    
        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test3.xnf" ) {
        auto clss = parse_file(xnf_path + "/xnfs/test3.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;
        slvr.get_opts()->ca = ca_alg::dpll;

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test3.xnf 2" ) {
        auto clss = parse_file(xnf_path + "/xnfs/test3.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test4.xnf" ) {
        auto clss = parse_file(xnf_path + "/xnfs/test4.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test5.xnf" ) {
        auto clss = parse_file(xnf_path + "/xnfs/test5.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test6.xnf" ) {
        auto clss = parse_file(xnf_path + "/xnfs/test6.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test7.xnf" ) {
        auto clss = parse_file(xnf_path + "/xnfs/test7.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test8.xnf" ) {
        auto clss = parse_file(xnf_path + "/xnfs/test8.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test9.xnf" ) {
        auto clss = parse_file(xnf_path + "/xnfs/test9.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test10.xnf" ) {
        auto clss = parse_file(xnf_path + "/xnfs/test10.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test11.xnf" ) {
        auto clss = parse_file(xnf_path + "/xnfs/test11.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test12.xnf" ) {
        auto clss = parse_file(xnf_path + "/xnfs/test12.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test13.xnf" ) {
        auto clss = parse_file(xnf_path + "/xnfs/test13.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.is_sat() == false ); //UNSAT!
    }
    
    SECTION( "test14.xnf" ) {
        auto clss = parse_file(xnf_path + "/xnfs/test14.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.is_sat() == false ); //UNSAT!
    }
    
    //SECTION( "test_hard.xnf" ) {
    //    auto clss = parse_file(xnf_path + "/xnfs/test_hard.xnf");
    //    auto slvr = solver(clss);
    //    slvr.get_opts()->verb = 90;

    //    stats s = slvr.solve();
    //    CHECK( s.is_sat() == true ); //SAT!
    //    CHECK( check_sols(clss.cls, s.sols) );
    //}
}

TEST_CASE( "solving 2xnf test instances with preprocessing" , "[solver][preprocessing]" ) {
    SECTION( "test_ascon.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test_ascon.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->pp = xornado_preproc::scc_fls;
        slvr.get_opts()->verb = 80;

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( s.no_dec == 0 );
    }
}

TEST_CASE( "solving 2xnf test instances with cdcl" , "[solver][cdcl]" ) {
    const bool cm = GENERATE(false, true);

    SECTION( "test0.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/cdcl/test0.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 80;
        slvr.get_opts()->cm = cm;
    
        stats s = slvr.solve();
        CHECK( s.is_sat() == false ); //instance is UNSAT
    }

    SECTION( "test1.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/cdcl/test1.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 0;
        slvr.get_opts()->cm = cm;
    
        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test2.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/cdcl/test2.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 0;
        slvr.get_opts()->cm = cm;
    
        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test3.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/cdcl/test3.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 0;
        slvr.get_opts()->cm = cm;
    
        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test4.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/cdcl/test4.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 0;
        slvr.get_opts()->cm = cm;
    
        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test61.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test61.xnf");
        options opt;
        opt.verb = 80;
        opt.ca = ca_alg::fuip;
        opt.ip = initial_prop_opt::nbu; //initial_prop_opt::no;
        opt.rst = restart_opt::luby;
        opt.dh = dec_heu::vsids;
        opt.gauss_elim_schedule = 0;
        opt.cm = cm;
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test55.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test55.xnf");
        options opt;
        opt.verb = 10;
        opt.ca = ca_alg::fuip;
        opt.ip = initial_prop_opt::nbu;
        opt.rst = cm ? restart_opt::luby : restart_opt::no;
        opt.dh = dec_heu::vsids;
        opt.gauss_elim_schedule = 0;
        opt.cm = cm;
        opt.verb = 80;
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test55.xnf 2" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test55.xnf");
        options opt;
        opt.verb = 80;
        opt.ca = ca_alg::no;
        opt.ip = initial_prop_opt::no;
        opt.pp = xornado_preproc::no;
        opt.rst = restart_opt::no;
        opt.dh = dec_heu::lex;
        opt.gauss_elim_schedule = 0;
        opt.cm = cm;
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test57.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test57.xnf");
        options opt;
        opt.verb = 80;
        opt.ca = ca_alg::fuip;
        opt.ip = initial_prop_opt::full;
        opt.rst = cm ? restart_opt::luby : restart_opt::no;
        opt.dh = dec_heu::vsids;
        opt.gauss_elim_schedule = 0;
        opt.cm = cm;
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test58.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test58.xnf");
        options opt;
        opt.verb = 80;
        opt.ca = ca_alg::fuip;
        opt.ip = initial_prop_opt::nbu;
        opt.rst = cm ? restart_opt::luby : restart_opt::no;
        opt.dh = dec_heu::vsids;
        opt.gauss_elim_schedule = 0;
        opt.cm = cm;
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test59.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test59.xnf");
        options opt;
        opt.verb = 80;
        opt.ca = ca_alg::fuip;
        opt.ip = initial_prop_opt::nbu;
        opt.rst = restart_opt::luby;
        opt.dh = dec_heu::vsids;
        opt.gauss_elim_schedule = 0;
        opt.cm = cm;
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test56.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test56.xnf");
        options opt;
        opt.verb = 80;
        opt.ca = ca_alg::fuip;
        opt.ip = initial_prop_opt::nbu;
        opt.rst = cm ? restart_opt::luby : restart_opt::no;
        opt.dh = dec_heu::vsids;
        opt.gauss_elim_schedule = 0;
        opt.cm = cm;
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
}

TEST_CASE( "solving 2xnf test instances with -ms", "[solver][maxsol][small]") {
    
    SECTION( "test36.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test36.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;
        slvr.get_opts()->ca = GENERATE(ca_alg::no, ca_alg::fuip_opt, ca_alg::fuip, ca_alg::dpll);
        slvr.get_opts()->sol_count = -1;

        stats s = slvr.solve();
        CHECK( s.sols.size() == 1 );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test37.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test37.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;
        slvr.get_opts()->ca = GENERATE(ca_alg::no, ca_alg::fuip_opt, ca_alg::fuip, ca_alg::dpll);
        slvr.get_opts()->sol_count = -1;

        stats s = slvr.solve();
        CHECK( s.sols.size() == 2 );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test38.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test38.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;
        slvr.get_opts()->ca = GENERATE(ca_alg::no, ca_alg::fuip_opt, ca_alg::fuip, ca_alg::dpll);
        slvr.get_opts()->sol_count = -1;

        stats s = slvr.solve();
        CHECK( s.sols.size() == 3 );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test10.xnf" ) {
        auto fname = xnf_path + "/2xnfs/test10.xnf";
        auto p_xnf = parse_file(fname);
        auto slvr = solver(p_xnf);

        SECTION("no gp") {

            (slvr.get_opts())->verb = 70;
            (slvr.get_opts())->ca = GENERATE(ca_alg::no, ca_alg::fuip_opt, ca_alg::fuip, ca_alg::dpll);
            SECTION("ms 1-5"){
                const auto sol_c = GENERATE(1,2,3,4,5);
                (slvr.get_opts())->sol_count = sol_c;

                stats s = slvr.solve();
                CHECK( check_sols(p_xnf.cls, s.sols) );
                CHECK( (int) s.sols.size() == sol_c );
            }
    
            SECTION("ms 6-7,all"){
                const auto sol_c = GENERATE(6,7,-1);
                (slvr.get_opts())->sol_count = sol_c;

                stats s = slvr.solve();
                CHECK( check_sols(p_xnf.cls, s.sols) );
                CHECK( (int) s.sols.size() == 6 );
            }
        }

        SECTION("with gp"){
            guessing_path P; P.insert(2);
            auto p_xnf_P = parse_file(fname);
            auto slvr_P = solver(p_xnf_P);

            (slvr_P.get_opts())->verb = 70;
            (slvr_P.get_opts())->ca = GENERATE(ca_alg::no, ca_alg::fuip, ca_alg::dpll);

            SECTION("ms 1-5"){
                const auto sol_c = GENERATE(1,2,3,4,5);
                (slvr_P.get_opts())->sol_count = sol_c;

                stats s = slvr_P.solve();
                CHECK( (int) s.sols.size() == sol_c );
                CHECK( check_sols(p_xnf_P.cls, s.sols) );
                CHECK( check_sols(p_xnf.cls, s.sols) );
            }
    
            SECTION("ms 6-7,all"){
                const auto sol_c = GENERATE(6,7,-1);
                (slvr_P.get_opts())->sol_count = sol_c;

                stats s = slvr_P.solve();
                CHECK( (int) s.sols.size() == 6 );
                CHECK( check_sols(p_xnf_P.cls, s.sols) );
                CHECK( check_sols(p_xnf.cls, s.sols) );
            }
        }
    }
    
    SECTION( "test46.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test46.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->sol_count = 2;

        stats s = slvr.solve();
        CHECK( s.is_sat() == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test40.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test40.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;
        slvr.get_opts()->ca = GENERATE(ca_alg::no, ca_alg::fuip_opt, ca_alg::fuip, ca_alg::dpll);
        slvr.get_opts()->sol_count = 2;

        stats s = slvr.solve();
        CHECK( s.sols.size() == 2 );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test41.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test41.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;
        slvr.get_opts()->ca = GENERATE(ca_alg::no, ca_alg::fuip_opt, ca_alg::fuip, ca_alg::dpll);
        slvr.get_opts()->sol_count = -1;
        slvr.get_opts()->gauss_elim_schedule = 2;

        stats s = slvr.solve(); //fails when 'remove_fixed_alpha()' is not run!
        CHECK( s.sols.size() == 3 );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test42.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test42.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;
        slvr.get_opts()->ca = ca_alg::no; //GENERATE(ca_alg::no, ca_alg::fuip_opt, ca_alg::fuip, ca_alg::dpll);
        slvr.get_opts()->sol_count = -1;
        slvr.get_opts()->gauss_elim_schedule = 1; //GENERATE(0,1,40);
        slvr.get_opts()->dh = dec_heu::lex; //GENERATE(dec_heu::lex, dec_heu::vsids);

        stats s = slvr.solve();
        CHECK( s.sols.size() == 8 );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test51.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test51.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;
        slvr.get_opts()->ca = ca_alg::fuip;
        slvr.get_opts()->sol_count = -1;
        slvr.get_opts()->gauss_elim_schedule = 20;
        slvr.get_opts()->dh = dec_heu::vsids;

        stats s = slvr.solve();
        CHECK( s.sols.size() == 5 );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test52.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test52.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;
        slvr.get_opts()->ca = ca_alg::fuip;
        slvr.get_opts()->sol_count = -1;
        slvr.get_opts()->gauss_elim_schedule = 0;
        slvr.get_opts()->dh = dec_heu::lex;

        stats s = slvr.solve();
        CHECK( s.sols.size() == 1 );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test60.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test60.xnf");
        options opt(dec_heu::lex, phase_opt::save, ca_alg::fuip, false, restart_opt::no, initial_prop_opt::nbu, true, 0, 0);
        opt.sol_count = -1;
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.is_sat() == true ); //SAT!
        CHECK( s.sols.size()==4 );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test62.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test62.xnf");
        options opt(dec_heu::vsids, phase_opt::save, ca_alg::fuip, false, restart_opt::no, initial_prop_opt::nbu, true, 0, 0);
        opt.sol_count = -1;
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sols.size()==1 );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test63.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test63.xnf");
        options opt(dec_heu::vsids, phase_opt::save, ca_alg::fuip, false, restart_opt::no, initial_prop_opt::nbu, true, 0, 0);
        opt.sol_count = -1;
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sols.size()==1 );
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test64.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test64.xnf");
        options opt(dec_heu::vsids, phase_opt::save, ca_alg::fuip, false, restart_opt::no, initial_prop_opt::nbu, true, 0, 0);
        opt.sol_count = -1;
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sols.size()==2 );
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test64.xnf 2" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test64.xnf");
        options opt(dec_heu::vsids, phase_opt::save, ca_alg::fuip, false, restart_opt::no, initial_prop_opt::nbu, true, 1, 0);
        opt.sol_count = -1;
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sols.size()==2 );
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test65.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test65.xnf");
        options opt(dec_heu::vsids, phase_opt::save, ca_alg::fuip, false, restart_opt::no, initial_prop_opt::nbu, true, 1, 0);
        opt.sol_count = -1;
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sols.size()==1 );
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test66.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test66.xnf");
        options opt(dec_heu::vsids, phase_opt::save, ca_alg::no, false, restart_opt::no, initial_prop_opt::nbu, true, 0, 0);
        opt.sol_count = -1;
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sols.size()==1 );
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test67.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test67.xnf");
        options opt(dec_heu::vsids, phase_opt::save, ca_alg::fuip, false, restart_opt::no, initial_prop_opt::nbu, true, 0, 0);
        opt.sol_count = -1;
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sols.size()==1 );
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test71.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test71.xnf");
        options opt(dec_heu::vsids, phase_opt::save, ca_alg::fuip, false, restart_opt::luby, initial_prop_opt::no, true, 0, 0);
        opt.sol_count = -1;
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sols.size()==5 );
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test68.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test68.xnf");
        options opt(dec_heu::vsids, phase_opt::save, ca_alg::fuip, false, restart_opt::luby, initial_prop_opt::nbu, true, 0, 0);
        opt.sol_count = -1;
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sols.size()==2 );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test73.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test73.xnf"); //one clause that is trivially satisfied
        CHECK(clss.num_cls==0);
        options opt(dec_heu::vsids, phase_opt::save, ca_alg::fuip, false, restart_opt::luby, initial_prop_opt::nbu, true, 0, 0);
        opt.sol_count = -1;
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sols.size()==4 );
        CHECK( check_sols(clss.cls, s.sols) );
    }

}

TEST_CASE( "solving harder instances", "[solver][maxsol][small][long]") {
    SECTION( "test_simon.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test_simon.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 10;
        slvr.get_opts()->ca = ca_alg::fuip;
        slvr.get_opts()->sol_count = 265;
        slvr.get_opts()->gauss_elim_schedule = 0;
        slvr.get_opts()->dh = dec_heu::vsids;
        slvr.get_opts()->rst = restart_opt::no;
        slvr.get_opts()->ip = GENERATE( initial_prop_opt::no, initial_prop_opt::nbu );

        stats s = slvr.solve();
        CHECK( s.sols.size() == 264 );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test_simon.xnf -la 28" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test_simon.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 85;
        slvr.get_opts()->ca = ca_alg::fuip;
        slvr.get_opts()->sol_count = 265;
        slvr.get_opts()->gauss_elim_schedule = 28;
        slvr.get_opts()->dh = dec_heu::vsids;
        slvr.get_opts()->rst = restart_opt::no;
        slvr.get_opts()->ip = GENERATE( initial_prop_opt::no, initial_prop_opt::nbu );

        stats s = slvr.solve();
        CHECK( s.sols.size() == 264 );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test_bivium.xnf" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test_bivium.xnf");
        options opt(dec_heu::vsids, phase_opt::save, ca_alg::fuip, false, restart_opt::no, initial_prop_opt::nbu, false, 3, 0);
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sols.size() == 1 );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test_simon_2.xnf -- 30s timeout" ) {
        auto clss = parse_file(xnf_path + "/2xnfs/test_simon_2.xnf");
        options opts(dec_heu::vsids, phase_opt::save, ca_alg::fuip, false, restart_opt::luby, initial_prop_opt::no, xornado_preproc::no, true, false, -1, 0, 30, 1, guessing_path());
        //timeout 30secs; bug appeared after about 20secs
        stats s = solve(clss.cls, clss.num_vars, opts);

        CHECK( (s.finished==false && s.no_restarts>1) );
    }

    SECTION( "test_prince.xnf -- 10s timeout" ) {
        auto clss = parse_file(xnf_path + "/xnfs/test_prince.xnf");
        options opts(dec_heu::vsids, phase_opt::save, ca_alg::fuip, 0, restart_opt::luby, initial_prop_opt::no, xornado_preproc::scc_fls, true, false, -1, 0, 10, 1, guessing_path());
        auto slvr = solver(clss, opts);

        stats s = slvr.solve();
        CHECK( check_sols(clss.cls, s.sols) );
    }

}

TEST_CASE("solving xnf instance with -ms","[solver][maxsol]") {
    
    SECTION("linear system") {
        auto fname = xnf_path + "/2xnfs/test34.xnf";

        auto p_xnf = parse_file(fname);
        auto slvr = solver(p_xnf);

        (slvr.get_opts())->verb = 70;
        (slvr.get_opts())->ca = GENERATE(ca_alg::no, ca_alg::fuip, ca_alg::dpll);
        const int sol_c = GENERATE(0,1,2,3,4,5,6,7,-1);
        (slvr.get_opts())->sol_count = sol_c;

        stats s = slvr.solve();
        CHECK( check_sols(p_xnf.cls, s.sols) );
        CHECK( (int) s.sols.size() == ( (0<=sol_c && sol_c<=6) ? (sol_c==0 ? 1 : sol_c) : 6) );
        std::set< vec<bool> > sols(s.sols.begin(), s.sols.end());
        CHECK( sols.size()==s.sols.size() );
    }
    
    SECTION("no gp") {
        auto fname = "../../benchmarks/generate_instances/enocoro_fa/eno_s4_mixed_quad.xnf";

        auto p_xnf = parse_file(fname);
        auto slvr = solver(p_xnf);

        (slvr.get_opts())->verb = 70;
        (slvr.get_opts())->ca = GENERATE(ca_alg::no, ca_alg::fuip, ca_alg::fuip_opt, ca_alg::dpll);
        const int sol_c = GENERATE(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,-1);
        (slvr.get_opts())->sol_count = sol_c;

        stats s = slvr.solve();
        CHECK( check_sols(p_xnf.cls, s.sols) );
        CHECK( (int) s.sols.size() == ( (0<=sol_c && sol_c<=16) ? (sol_c==0 ? 1 : sol_c) : 16) );
        std::set< vec<bool> > sols(s.sols.begin(), s.sols.end());
        CHECK( sols.size()==s.sols.size() );
    }
    
    SECTION("with gp") {
        auto fname = "../../benchmarks/generate_instances/enocoro_fa/eno_s4_mixed_quad.xnf";

        guessing_path P;
        P.insert(8);
        P.insert(7);
        P.insert(5);
        P.insert(6);
        P.insert(3);
        P.insert(1);
        P.insert(2);
        P.insert(4);
     
        auto p_xnf = parse_file(fname);
        auto slvr = solver(p_xnf);

        (slvr.get_opts())->verb = 70;
        (slvr.get_opts())->ca =ca_alg::fuip; //GENERATE(ca_alg::no, ca_alg::fuip, ca_alg::fuip_opt, ca_alg::dpll);
        const int sol_c = 9; //GENERATE(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,-1);
        (slvr.get_opts())->sol_count = sol_c;

        stats s = slvr.solve();
        CHECK( check_sols(p_xnf.cls, s.sols) );
        CHECK( (int) s.sols.size() == ( (0<=sol_c && sol_c<=16) ? (sol_c==0 ? 1 : sol_c) : 16) );
        std::set< vec<bool> > sols(s.sols.begin(), s.sols.end());
        CHECK( sols.size()==s.sols.size() );
    }
}

TEST_CASE( "read large instance", "[solver][parser]") {
    auto fname = xnf_path + "/2xnfs/test_read.xnf";
    auto p_xnf = parse_file(fname);
    options opts(dec_heu::vsids, phase_opt::save, ca_alg::fuip, false, restart_opt::luby, initial_prop_opt::no, xornado_preproc::no, true, true, -1, 0, 10, 1, guessing_path());
    stats s = solve(p_xnf.cls, p_xnf.num_vars, opts);

    CHECK( s.no_dec>10 ); //solving takes too long at the moment -- but: check that solving even started! (previously took ages for init!)
    //CHECK( s.is_sat() == true );
    //CHECK( check_sols(p_xnf.cls, s.sols) );
}

TEST_CASE( "solving simple instances", "[solver]") {
    auto fname = GENERATE(xnf_path + "/2xnfs/rand/rand-10-20.xnf", xnf_path + "/2xnfs/cdcl/tmpgvgj2vfs.xnf", xnf_path + "/2xnfs/cdcl/tmp3bjwevbm.xnf", xnf_path + "/2xnfs/cdcl/tmpxwh016x1.xnf", xnf_path + "/2xnfs/cdcl/tmpe4wzt2ga.xnf", xnf_path + "/2xnfs/mq/toyexamples/ToyExample-type4-n10-seed0.xnf", xnf_path + "/2xnfs/cdcl/tmpzw1cx_np.xnf" );
    auto p_xnf = parse_file(fname);
    auto slvr = solver(p_xnf);

    (slvr.get_opts())->verb = 70;

    stats s = slvr.solve();
    CHECK( s.is_sat() == true ); //SAT!
    CHECK( check_sols(p_xnf.cls, s.sols) );
}

TEST_CASE( "solving with different options" , "[parser][solve]" ) {
    auto fname = GENERATE(xnf_path + "/2xnfs/mq/toyexamples/ToyExample-type1-n10-seed0.xnf", xnf_path + "/2xnfs/rand/rand-3-6.xnf", xnf_path + "/2xnfs/rand/rand-10-20.xnf", xnf_path + "/2xnfs/rand/rand-20-40.xnf");
    //auto fname = xnf_path + "/2xnfs/rand/rand-20-40.xnf";
    //auto fname = xnf_path + "/2xnfs/rand/rand-10-20.xnf";
    //auto fname = xnf_path + "/2xnfs/rand/rand-3-6.xnf";
    //auto fname = xnf_path + "/2xnfs/mq/toyexamples/ToyExample-type1-n10-seed0.xnf";
    auto clss = parse_file( fname );
    auto xnf = clss.cls;
    var_t num_vars = clss.num_vars;
    dec_heu dh = GENERATE(dec_heu::vsids, dec_heu::lex);
    phase_opt po = GENERATE(phase_opt::rand, phase_opt::save, phase_opt::save_inv);
    ca_alg ca = ca_alg::no; //GENERATE(ca_alg::no, ca_alg::fuip);
    int la_sch = 10; //GENERATE(0,1,10);
    options opts(dh, po, ca, la_sch, 0, 0);

    stats s = solve(xnf, num_vars, opts);
    CHECK( s.is_sat() == true ); //SAT
    CHECK( check_sols(clss.cls, s.sols) );
}


TEST_CASE( "solving within timeout" , "[parser][solve]" ) {
    auto fname = GENERATE(xnf_path + "/2xnfs/mq/toyexamples/ToyExample-type1-n10-seed0.xnf", xnf_path + "/2xnfs/rand/rand-3-6.xnf", xnf_path + "/2xnfs/rand/rand-10-20.xnf", xnf_path + "/2xnfs/rand/rand-20-40.xnf");
    //auto fname = xnf_path + "/2xnfs/rand/rand-20-40.xnf";
    //auto fname = xnf_path + "/2xnfs/rand/rand-10-20.xnf";
    //auto fname = xnf_path + "/2xnfs/rand/rand-3-6.xnf";
    //auto fname = xnf_path + "/2xnfs/mq/toyexamples/ToyExample-type1-n10-seed0.xnf";
    auto clss = parse_file( fname );
    auto xnf = clss.cls;
    auto num_vars = clss.num_vars;

    options opts(dec_heu::vsids, phase_opt::save, ca_alg::fuip, 100, 0, 0);
    std::chrono::high_resolution_clock::time_point begin = std::chrono::high_resolution_clock::now();
    stats s = solve(xnf, num_vars, opts);
    std::chrono::high_resolution_clock::time_point end = std::chrono::high_resolution_clock::now();
    float time_no_time_out = static_cast<float>(std::chrono::duration_cast<std::chrono::milliseconds>(end - begin).count())/1000.0f;

    options opts2(dec_heu::vsids, phase_opt::save, ca_alg::fuip, 100, 0, time_no_time_out+3);
    begin = std::chrono::high_resolution_clock::now();
    stats s2 = solve(xnf, num_vars, opts2);
    end = std::chrono::high_resolution_clock::now();
    float time_with_time_out = static_cast<float>(std::chrono::duration_cast<std::chrono::milliseconds>(end - begin).count())/1000.0f;
  #ifdef NDEBUG
    CHECK( time_no_time_out == Catch::Approx(time_with_time_out).margin(0.1) );
  #else
    CHECK( time_no_time_out == Catch::Approx(time_with_time_out).margin(5) );
  #endif
    CHECK( s.finished == true ); //SAT
    CHECK( s.is_sat() == true ); //SAT
    CHECK( check_sols(clss.cls, s.sols) );
}

TEST_CASE("solving with different options -- timeout", "[parser][solve]")  {
  #ifdef NDEBUG
    auto clss = parse_file(xnf_path + "/2xnfs/mq/challenge-1-55-0.xnf");
  #else
    auto clss = parse_file(xnf_path + "/2xnfs/mq/toyexamples/ToyExample-type1-n20-seed0.xnf");
  #endif
    auto xnf = clss.cls;
    auto num_vars = clss.num_vars;

    options opts(dec_heu::vsids, phase_opt::save, ca_alg::fuip, 50, 0, 1);
    stats s = solve(xnf, num_vars, opts);

    CHECK( s.finished == false );
}
