//file to test implementation of solve
#include "../src/solve.hpp"
#include "../src/solver.hpp"

#include <catch2/catch_all.hpp>

TEST_CASE( "solving test instances" , "[solver]" ) {
    SECTION( "test1.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test1.xnf");
        auto slvr = solver(clss);
    
        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //UNSAT
        //CHECK( s.sol == vec<bool>({false,false,false}) );
        CHECK( check_sol(clss.cls, s.sol) );
    }

    SECTION( "test2.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test2.xnf");
        auto slvr = solver(clss);
        CHECK( slvr.to_str() == "x1 x3+1; x1+1 x2+x3; x2 x3+1; x2+1 x1+x3;" );
        //CHECK( slvr.to_str() == "x1 x3+1; x1+1 x2+x3; x1+x3 x2+1; x2 x3+1;" );
    
        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //UNSAT
        //CHECK( s.sol == vec<bool>({false,false,false}) );
        CHECK( check_sol(clss.cls, s.sol) );
    }

    SECTION( "test3.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test3.xnf");
        auto slvr = solver(clss);
        //CHECK( slvr.to_str() == "x1+x5 x2+x5 x3+x5 x4+x5 1" );
        CHECK( slvr.to_str() == "" );
    
        stats s = slvr.dpll_solve();
        CHECK( s.sat == false ); //UNSAT
    }
    
    SECTION( "test18.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test18.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 90;

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test5.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test5.xnf");
        auto slvr = solver(clss);

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        //CHECK( s.sol == vec<bool>({false,false,false,false,false}) );
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test6.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test6.xnf");
        auto slvr = solver(clss);

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        //CHECK( s.sol == vec<bool>({false,false}) );
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test6_.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test6_.xnf");
        auto slvr = solver(clss);

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true );
        CHECK( s.sol == vec<bool>({false,true}) );
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test7.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test7.xnf");
        auto slvr = solver(clss);

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true );
        //CHECK( s.sol == vec<bool>({true,false,false,true,true}) );
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test8.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test8.xnf");
        auto slvr = solver(clss);

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        //CHECK( s.sol == vec<bool>({true,true,true}) );
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test9.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test9.xnf");
        auto slvr = solver(clss);

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        //CHECK( s.sol == vec<bool>({true,false,true,false,false}) );
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test10.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test10.xnf");
        auto slvr = solver(clss);

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        //CHECK( s.sol == vec<bool>({true,true,false,false}) );
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test11.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test11.xnf");
        auto slvr = solver(clss);

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        //CHECK( s.sol == vec<bool>({false}) );
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test12.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test12.xnf");
        auto slvr = solver(clss);

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test13.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test13.xnf");
        auto slvr = solver(clss);

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test14.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test14.xnf");
        auto slvr = solver(clss);
        //CHECK( slvr.to_str() == "x2 x1+x2; x2+1 x1+x2+1;0" );
        //CHECK( slvr.to_str() == "x2 x1+x2; x2+1 x1+x2+1;" );
        //CHECK( slvr.to_str() == "x2 x1+x2; x2+1 x1+1;" );

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test15.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test15.xnf");
        auto slvr = solver(clss);
        //CHECK( slvr.to_str() == "x1+x2 x1+1; x2+1 x1+x2+1;x2+1" );
        //CHECK( slvr.to_str() == "x1+x2 x1+1; x2+1 x1+x2+1;" );
        //CHECK( slvr.to_str() == "x1+1 x2; x2+1 x1+1;" );

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test16.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test16.xnf");
        auto slvr = solver(clss);

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test17.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test17.xnf");
        auto slvr = solver(clss);

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test4.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test4.xnf");
        auto slvr = solver(clss);
        CHECK( slvr.to_str() == "x1 x2+1; x2 x3+1; x3 x4+1; x3+x5 x6; x4 x5+x6+1; x5+x6 x1+1; x6+1 x7+1; x7 x3+x5+1;" );
        //CHECK( slvr.to_str() == "x1 x2+1; x1+1 x5+x6; x2 x3+1; x3 x4+1; x3+x5 x6; x3+x5+1 x7; x4 x5+x6+1; x6+1 x7+1;" );
        
        stats s = slvr.dpll_solve();
        CHECK( s.sat == false ); //UNSAT!
    }
    
    SECTION( "test19.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test19.xnf");
        auto slvr = solver(clss);

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test20.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test20.xnf");
        auto slvr = solver(clss);

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sol(clss.cls, s.sol) );
    }

    SECTION( "test21.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test21.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 90;

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sol(clss.cls, s.sol) );
    }

    SECTION( "test22.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test22.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 90;

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sol(clss.cls, s.sol) );
    }

    SECTION( "test23.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test23.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 90;

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test24.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test24.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 90;

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test25.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test25.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 90;

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test26.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test26.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 90;

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "test27.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test27.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 90;

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sol(clss.cls, s.sol) );
    }

    SECTION( "test28.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test28.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 90;

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sol(clss.cls, s.sol) );
    }

    SECTION( "rand-3-6.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/rand/rand-3-6.xnf");
        auto slvr = solver(clss);

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "../../benchmarks/instances/2xnfs/cdcl/tmpzw1cx_np.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/cdcl/tmpzw1cx_np.xnf");
        auto slvr = solver(clss);

        stats s = slvr.dpll_solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sol(clss.cls, s.sol) );
    }
}



TEST_CASE( "solving simple instances", "[solver]") {
    auto fname = GENERATE("../../benchmarks/instances/2xnfs/rand/rand-10-20.xnf", "../../benchmarks/instances/2xnfs/cdcl/tmpgvgj2vfs.xnf", "../../benchmarks/instances/2xnfs/cdcl/tmp3bjwevbm.xnf", "../../benchmarks/instances/2xnfs/cdcl/tmpxwh016x1.xnf", "../../benchmarks/instances/2xnfs/cdcl/tmpe4wzt2ga.xnf", "../../benchmarks/instances/2xnfs/mq/toyexamples/ToyExample-type4-n10-seed0.xnf", "../../benchmarks/instances/2xnfs/cdcl/tmpzw1cx_np.xnf" );
    auto p_xnf = parse_file(fname);
    auto slvr = solver(p_xnf);

    (slvr.get_opts())->verb = 70;

    stats s = slvr.dpll_solve();
    CHECK( s.sat == true ); //SAT!
    CHECK( check_sol(p_xnf.cls, s.sol) );
}

TEST_CASE( "solving with different options" , "[impl-graph][graph][parser][solve]" ) {
    auto fname = GENERATE("../../benchmarks/instances/2xnfs/mq/toyexamples/ToyExample-type1-n10-seed0.xnf", "../../benchmarks/instances/2xnfs/rand/rand-3-6.xnf", "../../benchmarks/instances/2xnfs/rand/rand-10-20.xnf", "../../benchmarks/instances/2xnfs/rand/rand-20-40.xnf");
    //auto fname = "../../benchmarks/instances/2xnfs/rand/rand-20-40.xnf";
    //auto fname = "../../benchmarks/instances/2xnfs/rand/rand-10-20.xnf";
    //auto fname = "../../benchmarks/instances/2xnfs/rand/rand-3-6.xnf";
    //auto fname = "../../benchmarks/instances/2xnfs/mq/toyexamples/ToyExample-type1-n10-seed0.xnf";
    auto clss = parse_file( fname );
    auto xnf = clss.cls;
    var_t num_vars = clss.num_vars;
    var_t num_cls = clss.num_cls;

    SECTION( "dh:vsids-fls:no-upd:ts" ) {
        options opts(num_vars, num_cls, dec_heu::vsids, phase_opt::save, ca_alg::fuip, 1, 0, 0);
        stats s = solve(xnf, opts);
        CHECK( s.sat == true ); //SAT
        CHECK( check_sol(clss.cls, s.sol) );
    }

    SECTION( "dh:vsids-fls:full-upd:ts" ) {
        options opts(num_vars, num_cls, dec_heu::vsids, phase_opt::save, ca_alg::fuip, 1, 0, 0);
        stats s = solve(xnf, opts);
        CHECK( s.sat == true ); //SAT
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "dh:vsids-fls:full-upd:hf" ) {
        options opts(num_vars, num_cls, dec_heu::vsids, phase_opt::save, ca_alg::fuip, 1, 0, 0);
        stats s = solve(xnf, opts);
        CHECK( s.sat == true ); //SAT
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "dh:vsids-fls:trivial-upd:hf" ) {
        options opts(num_vars, num_cls, dec_heu::vsids, phase_opt::save, ca_alg::fuip, 1, 0, 0);
        stats s = solve(xnf, opts);
        CHECK( s.sat == true ); //SAT
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "dh:vsids-fls:trivial-upd:hfd" ) {
        options opts(num_vars, num_cls, dec_heu::lwl, phase_opt::save, ca_alg::fuip, 1, 0, 0);
        stats s = solve(xnf, opts);
        CHECK( s.sat == true ); //SAT
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "dh:vsids-fls:trivial-upd:hf -- 4 jobs" ) {
        options opts(num_vars, num_cls, dec_heu::vsids, phase_opt::save, ca_alg::fuip, 4, 0, 0);
        stats s = solve(xnf, opts);
        CHECK( s.sat == true ); //SAT
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "dh:vsids-fls:trivial-upd:par -- 4 jobs" ) {
        options opts(num_vars, num_cls, dec_heu::vsids, phase_opt::save, ca_alg::fuip, 4, 0, 0);
        stats s = solve(xnf, opts);
        CHECK( s.sat == true ); //SAT
        CHECK( check_sol(clss.cls, s.sol) );
    }
    
    SECTION( "dh:vsids-fls:trivial-upd:hf -- terminate within timeout" ) {
        options opts(num_vars, num_cls, dec_heu::vsids, phase_opt::save, ca_alg::fuip, 1, 0, 0);
        std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
        stats s = solve(xnf, opts);
        std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
        float time_no_time_out = static_cast<float>(std::chrono::duration_cast<std::chrono::milliseconds>(end - begin).count())/1000.0f;

        options opts2(num_vars, num_cls, dec_heu::vsids, phase_opt::save, ca_alg::fuip, 1, 0, time_no_time_out+3);
        begin = std::chrono::steady_clock::now();
        stats s2 = solve(xnf, opts2);
        end = std::chrono::steady_clock::now();
        float time_with_time_out = static_cast<float>(std::chrono::duration_cast<std::chrono::milliseconds>(end - begin).count())/1000.0f;
        CHECK( time_no_time_out == Catch::Approx(time_with_time_out).margin(0.1) );

        CHECK( s.finished == true ); //SAT
        CHECK( s.sat == true ); //SAT
        CHECK( check_sol(clss.cls, s.sol) );
    }
}

TEST_CASE("solving with different options -- timeout", "[impl-graph][graph][parser][solve]")  {
  #ifdef NDEBUG
    auto clss = parse_file("../../benchmarks/instances/2xnfs/mq/challenge-1-55-0.xnf");
  #else
    auto clss = parse_file("../../benchmarks/instances/2xnfs/mq/toyexamples/ToyExample-type1-n20-seed0.xnf");
  #endif
    auto xnf = clss.cls;
    auto num_vars = clss.num_vars;
    auto num_cls = clss.num_cls;

    options opts(num_vars, num_cls, dec_heu::vsids, phase_opt::save, ca_alg::fuip, 1, 0, 1);
    stats s = solve(xnf, opts);

    CHECK( s.finished == false );
}