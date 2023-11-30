//file to test implementation of solve
#include "../src/solve.hpp"
#include "../src/solver.hpp"

#include <catch2/catch_all.hpp>

TEST_CASE( "solving 2xnf test instances" , "[solver]" ) {
  #ifndef NDEBUG
    int la_sch = GENERATE(0,1,5);
    dec_heu dh = GENERATE(dec_heu::vsids, dec_heu::lex);
    phase_opt po = phase_opt::save; //GENERATE(phase_opt::rand, phase_opt::save, phase_opt::save_inv);
    ca_alg ca = GENERATE(ca_alg::no, ca_alg::fuip, ca_alg::fuip_opt);
    int verb = 80;
  #else
    int la_sch = GENERATE(0,1,5,10);
    dec_heu dh = GENERATE(dec_heu::vsids, dec_heu::lwl, dec_heu::swl, dec_heu::lex);
    phase_opt po = GENERATE(phase_opt::rand, phase_opt::save, phase_opt::save_inv);
    ca_alg ca = GENERATE(ca_alg::dpll, ca_alg::no, ca_alg::fuip, ca_alg::fuip_opt);
    int verb = 0;
  #endif

    options opt(dh, po, ca, la_sch, verb);

    SECTION( "test1.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test1.xnf");
        auto slvr = solver(clss, opt);
    
        stats s = slvr.solve();
        CHECK( s.sat == true ); //UNSAT
        //CHECK( s.sol == vec<bool>({false,false,false}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test2.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test2.xnf");
        auto slvr = solver(clss, opt);
        CHECK( slvr.to_str() == "x1 x3+1; x1+1 x2+x3; x2 x3+1; x2+1 x1+x3;" );
        //CHECK( slvr.to_str() == "x1 x3+1; x1+1 x2+x3; x1+x3 x2+1; x2 x3+1;" );
    
        stats s = slvr.solve();
        CHECK( s.sat == true ); //UNSAT
        //CHECK( s.sol == vec<bool>({false,false,false}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test3.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test3.xnf");
        auto slvr = solver(clss, opt);
        //CHECK( slvr.to_str() == "x1+x5 x2+x5 x3+x5 x4+x5 1" );
        CHECK( slvr.to_str() == "" );
    
        stats s = slvr.solve();
        CHECK( s.sat == false ); //UNSAT
    }
    
    SECTION( "test18.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test18.xnf");
        auto slvr = solver(clss, opt);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test5.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test5.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        //CHECK( s.sol == vec<bool>({false,false,false,false,false}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test6.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test6.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        //CHECK( s.sol == vec<bool>({false,false}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test6_.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test6_.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sat == true );
        CHECK( s.sols.back() == vec<bool>({false,true}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test7.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test7.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sat == true );
        //CHECK( s.sol == vec<bool>({true,false,false,true,true}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test8.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test8.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        //CHECK( s.sol == vec<bool>({true,true,true}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test9.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test9.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        //CHECK( s.sol == vec<bool>({true,false,true,false,false}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test10.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test10.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        //CHECK( s.sol == vec<bool>({true,true,false,false}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test11.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test11.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        //CHECK( s.sol == vec<bool>({false}) );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test12.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test12.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test13.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test13.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test14.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test14.xnf");
        auto slvr = solver(clss, opt);
        //CHECK( slvr.to_str() == "x2 x1+x2; x2+1 x1+x2+1;0" );
        //CHECK( slvr.to_str() == "x2 x1+x2; x2+1 x1+x2+1;" );
        //CHECK( slvr.to_str() == "x2 x1+x2; x2+1 x1+1;" );

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test15.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test15.xnf");
        auto slvr = solver(clss, opt);
        //CHECK( slvr.to_str() == "x1+x2 x1+1; x2+1 x1+x2+1;x2+1" );
        //CHECK( slvr.to_str() == "x1+x2 x1+1; x2+1 x1+x2+1;" );
        //CHECK( slvr.to_str() == "x1+1 x2; x2+1 x1+1;" );

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test16.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test16.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test17.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test17.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test4.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test4.xnf");
        auto slvr = solver(clss, opt);
        CHECK( slvr.to_str() == "x1 x2+1; x2 x3+1; x3 x4+1; x3+x5 x6; x4 x5+x6+1; x5+x6 x1+1; x6+1 x7+1; x7 x3+x5+1;" );
        //CHECK( slvr.to_str() == "x1 x2+1; x1+1 x5+x6; x2 x3+1; x3 x4+1; x3+x5 x6; x3+x5+1 x7; x4 x5+x6+1; x6+1 x7+1;" );
        
        stats s = slvr.solve();
        CHECK( s.sat == false ); //UNSAT!
    }
    
    SECTION( "test19.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test19.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test20.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test20.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test21.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test21.xnf");
        auto slvr = solver(clss, opt);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test22_.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test22_.xnf");
        auto slvr = solver(clss, opt);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test22.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test22.xnf");
        auto slvr = solver(clss, opt);
        assert( slvr.assert_data_structs() );
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test23.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test23.xnf");
        auto slvr = solver(clss, opt);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test24.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test24.xnf");
        auto slvr = solver(clss, opt);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test25.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test25.xnf");
        auto slvr = solver(clss, opt);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test26.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test26.xnf");
        auto slvr = solver(clss, opt);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test27.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test27.xnf");
        auto slvr = solver(clss, opt);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test28.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test28.xnf");
        auto slvr = solver(clss, opt);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test29.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test29.xnf");
        auto slvr = solver(clss, opt);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test30.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test30.xnf");
        auto slvr = solver(clss, opt);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test31.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test31.xnf");
        auto slvr = solver(clss, opt);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "rand-3-6.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/rand/rand-3-6.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "../../benchmarks/instances/2xnfs/cdcl/tmpzw1cx_np.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/cdcl/tmpzw1cx_np.xnf");
        auto slvr = solver(clss, opt);

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test32.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test32.xnf");
        auto slvr = solver(clss, opt);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    
    SECTION( "test35.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test35.xnf");
        auto slvr = solver(clss, opt);
        slvr.get_opts()->verb = 90;
        slvr.get_opts()->ca = ca_alg::fuip_opt;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test36.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test36.xnf");
        auto slvr = solver(clss, opt);
        slvr.get_opts()->verb = 90;
        slvr.get_opts()->ca = ca_alg::fuip_opt;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test37.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test37.xnf");
        auto slvr = solver(clss, opt);
        slvr.get_opts()->verb = 90;
        slvr.get_opts()->ca = ca_alg::fuip_opt;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test38.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test38.xnf");
        auto slvr = solver(clss, opt);
        slvr.get_opts()->verb = 90;
        slvr.get_opts()->ca = ca_alg::fuip_opt;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test39.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test39.xnf");
        auto slvr = solver(clss, opt);
        slvr.get_opts()->verb = 90;
        slvr.get_opts()->ca = ca_alg::fuip_opt;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
}

TEST_CASE( "solving 2xnf test instances with gp" , "[solver][gp]" ) {
    SECTION( "test33.xnf" ) {
        reordering P;
        P.insert(2);
        P.insert(1);
        P.insert(4);
        P.insert(5);
        P.insert(3);
        CHECK( P.assert_data_struct() );
        auto clss_gp = parse_file_gp("../../benchmarks/instances/2xnfs/test33.xnf", P);
        auto slvr_gp = solver(clss_gp, P);
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test33.xnf");
        auto slvr = solver(clss);

        stats s_gp = slvr_gp.solve();
        stats s = slvr.solve();

        CHECK( s.sat == true ); //SAT!
        CHECK( s_gp.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
        CHECK( check_sols(clss_gp.cls, s_gp.sols) );

        //check that after reordering sol of s_gp, we get a sol of original clss
        CHECK( !check_sols(clss.cls, s_gp.sols) );
        s_gp.reorder_sols(P);
        CHECK( check_sols(clss.cls, s_gp.sols) );
    }
    
    SECTION( "test33.xnf II" ) {
        reordering P;
        P.insert(2);
        P.insert(1);
        P.insert(4);
        P.insert(5);
        P.insert(3);
        P.insert(7);
        P.insert(8);
        P.insert(6);
        CHECK( P.assert_data_struct() );
        auto clss_gp = parse_file_gp("../../benchmarks/instances/2xnfs/test33.xnf", P);
        auto slvr_gp = solver(clss_gp, P);
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test33.xnf");
        auto slvr = solver(clss);

        stats s_gp = slvr_gp.solve();
        stats s = slvr.solve();

        CHECK( s.sat == true ); //SAT!
        CHECK( s_gp.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
        CHECK( check_sols(clss_gp.cls, s_gp.sols) );

        //check that after reordering sol of s_gp, we get a sol of original clss
        CHECK( !check_sols(clss.cls, s_gp.sols) );
        s_gp.reorder_sols(P);
        CHECK( check_sols(clss.cls, s_gp.sols) );
    }
    
    SECTION( "flat30-100.xnf" ) {
        reordering P;
        P.insert(2);
        P.insert(1);
        P.insert(10);
        P.insert(11);
        P.insert(83);
        P.insert(74);
        CHECK( P.assert_data_struct() );
        //auto P = parse_gp("gp");
        auto clss_gp = parse_file_gp("../../benchmarks/instances/2xnfs/flat/flat30-100.xnf", P);
        auto slvr_gp = solver(clss_gp, P);
        auto clss = parse_file("../../benchmarks/instances/2xnfs/flat/flat30-100.xnf");
        auto slvr = solver(clss);

        stats s_gp = slvr_gp.solve();
        stats s = slvr.solve();

        CHECK( s.sat == true ); //SAT!
        CHECK( s_gp.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
        CHECK( check_sols(clss_gp.cls, s_gp.sols) );

        //check that after reordering sol of s_gp, we get a sol of original clss
        CHECK( !check_sols(clss.cls, s_gp.sols) );
        s_gp.reorder_sols(P);
        CHECK( check_sols(clss.cls, s_gp.sols) );
    }
    
    SECTION( "test10.xnf" ) {
        reordering P;
        P.insert(1, bool3::True);
        CHECK( P.assert_data_struct() );
        //auto P = parse_gp("gp");
        auto clss_gp = parse_file_gp("../../benchmarks/instances/2xnfs/test10.xnf", P);
        auto slvr_gp = solver(clss_gp, P);
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test10.xnf");
        auto slvr = solver(clss);

        stats s_gp = slvr_gp.solve();
        stats s = slvr.solve();

        CHECK( s.sat == true ); //SAT!
        CHECK( s_gp.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
        CHECK( check_sols(clss_gp.cls, s_gp.sols) );

        //check that after reordering sol of s_gp, we get a sol of original clss
        CHECK( s.sols.front() != s_gp.sols.front() );
    }
    
    SECTION( "eno_s4_mixed_quad.xnf" ) {
        reordering P;
        P.insert(1, bool3::False);
        P.insert(2, bool3::True);
        P.insert(3, bool3::False);
        P.insert(4, bool3::True);
        CHECK( P.assert_data_struct() );
        //auto P = parse_gp("gp");
        auto clss_gp = parse_file_gp("../../benchmarks/generate_instances/enocoro_fa/eno_s4_mixed_quad.xnf", P);
        auto slvr_gp = solver(clss_gp, P);

        stats s_gp = slvr_gp.solve();

        CHECK( s_gp.sat == true ); //SAT!
        CHECK( check_sols(clss_gp.cls, s_gp.sols) );

        //check that after reordering sol of s_gp, we get a sol of original clss
        CHECK( s_gp.sols.front() == vec<bool>({false, true, false, true, true, true, true, false}) );
    }
}

TEST_CASE( "solving xnf test instances" , "[solver]" ) {
    SECTION( "test1.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/xnfs/test1.xnf");
        auto slvr = solver(clss);
    
        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test2.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/xnfs/test2.xnf");
        auto slvr = solver(clss);
    
        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test3.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/xnfs/test3.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test4.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/xnfs/test4.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test5.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/xnfs/test5.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test6.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/xnfs/test6.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test7.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/xnfs/test7.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test8.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/xnfs/test8.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test9.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/xnfs/test9.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test10.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/xnfs/test10.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test11.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/xnfs/test11.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test12.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/xnfs/test12.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 90;

        stats s = slvr.solve();
        CHECK( s.sat == true ); //SAT!
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    //SECTION( "test_hard.xnf" ) {
    //    auto clss = parse_file("../../benchmarks/instances/xnfs/test_hard.xnf");
    //    auto slvr = solver(clss);
    //    slvr.get_opts()->verb = 90;

    //    stats s = slvr.solve();
    //    CHECK( s.sat == true ); //SAT!
    //    CHECK( check_sols(clss.cls, s.sols) );
    //}
}

TEST_CASE( "solving 2xnf test instances with cdcl" , "[solver][cdcl]" ) {
    SECTION( "test0.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/cdcl/test0.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 100;
    
        stats s = slvr.solve();
        CHECK( s.sat == false ); //instance is UNSAT
    }

    SECTION( "test1.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/cdcl/test1.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 100;
    
        stats s = slvr.solve();
        CHECK( s.sat == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }

    SECTION( "test2.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/cdcl/test2.xnf");
        auto slvr = solver(clss);
    
        stats s = slvr.solve();
        CHECK( s.sat == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test3.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/cdcl/test3.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 100;
    
        stats s = slvr.solve();
        CHECK( s.sat == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test4.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/cdcl/test4.xnf");
        auto slvr = solver(clss);
        slvr.get_opts()->verb = 100;
    
        stats s = slvr.solve();
        CHECK( s.sat == true );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
}

TEST_CASE( "solving 2xnf test instances with -ms", "[solver][maxsol][small]") {
    
    SECTION( "test36.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test36.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;
        slvr.get_opts()->ca = GENERATE(ca_alg::no, ca_alg::fuip_opt, ca_alg::fuip, ca_alg::dpll);
        slvr.get_opts()->sol_count = -1;

        stats s = slvr.solve();
        CHECK( s.sols.size() == 1 );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test37.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test37.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;
        slvr.get_opts()->ca = GENERATE(ca_alg::no, ca_alg::fuip_opt, ca_alg::fuip, ca_alg::dpll);
        slvr.get_opts()->sol_count = -1;

        stats s = slvr.solve();
        CHECK( s.sols.size() == 2 );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test38.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test38.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;
        slvr.get_opts()->ca = GENERATE(ca_alg::no, ca_alg::fuip_opt, ca_alg::fuip, ca_alg::dpll);
        slvr.get_opts()->sol_count = -1;

        stats s = slvr.solve();
        CHECK( s.sols.size() == 3 );
        CHECK( check_sols(clss.cls, s.sols) );
    }
    
    SECTION( "test10.xnf" ) {
        auto fname = "../../benchmarks/instances/2xnfs/test10.xnf";
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
            reordering P; P.insert(2);
            auto p_xnf_P = parse_file_gp(fname, P);
            auto slvr_P = solver(p_xnf_P);

            (slvr_P.get_opts())->verb = 70;
            (slvr_P.get_opts())->ca = GENERATE(ca_alg::no, ca_alg::fuip, ca_alg::dpll);

            SECTION("ms 1-5"){
                const auto sol_c = GENERATE(1,2,3,4,5);
                (slvr_P.get_opts())->sol_count = sol_c;

                stats s = slvr_P.solve();
                CHECK( (int) s.sols.size() == sol_c );
                CHECK( check_sols(p_xnf_P.cls, s.sols) );
                s.reorder_sols(P);
                CHECK( check_sols(p_xnf.cls, s.sols) );
            }
    
            SECTION("ms 6-7,all"){
                const auto sol_c = GENERATE(6,7,-1);
                (slvr_P.get_opts())->sol_count = sol_c;

                stats s = slvr_P.solve();
                CHECK( (int) s.sols.size() == 6 );
                CHECK( check_sols(p_xnf_P.cls, s.sols) );
                s.reorder_sols(P);
                CHECK( check_sols(p_xnf.cls, s.sols) );
            }
        }
    }
    
    SECTION( "test40.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/2xnfs/test40.xnf");
        auto slvr = solver(clss);
        //slvr.get_opts()->verb = 90;
        slvr.get_opts()->ca = GENERATE(ca_alg::no, ca_alg::fuip_opt, ca_alg::fuip, ca_alg::dpll);
        slvr.get_opts()->sol_count = 2;

        stats s = slvr.solve();
        CHECK( s.sols.size() == 2 );
        CHECK( check_sols(clss.cls, s.sols) );
    }
}

TEST_CASE("solving xnf instance with -ms","[solver][maxsol]") {
    
    SECTION("linear system") {
        auto fname = "../../benchmarks/instances/2xnfs/test34.xnf";

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

        reordering P;
        P.insert(8);
        P.insert(7);
        P.insert(5);
        P.insert(6);
        P.insert(3);
        P.insert(1);
        P.insert(2);
        P.insert(4);
     
        auto p_xnf = parse_file_gp(fname, P);
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

TEST_CASE( "solving simple instances", "[solver]") {
    auto fname = GENERATE("../../benchmarks/instances/2xnfs/rand/rand-10-20.xnf", "../../benchmarks/instances/2xnfs/cdcl/tmpgvgj2vfs.xnf", "../../benchmarks/instances/2xnfs/cdcl/tmp3bjwevbm.xnf", "../../benchmarks/instances/2xnfs/cdcl/tmpxwh016x1.xnf", "../../benchmarks/instances/2xnfs/cdcl/tmpe4wzt2ga.xnf", "../../benchmarks/instances/2xnfs/mq/toyexamples/ToyExample-type4-n10-seed0.xnf", "../../benchmarks/instances/2xnfs/cdcl/tmpzw1cx_np.xnf" );
    auto p_xnf = parse_file(fname);
    auto slvr = solver(p_xnf);

    (slvr.get_opts())->verb = 70;

    stats s = slvr.solve();
    CHECK( s.sat == true ); //SAT!
    CHECK( check_sols(p_xnf.cls, s.sols) );
}

TEST_CASE( "solving with different options" , "[parser][solve]" ) {
    auto fname = GENERATE("../../benchmarks/instances/2xnfs/mq/toyexamples/ToyExample-type1-n10-seed0.xnf", "../../benchmarks/instances/2xnfs/rand/rand-3-6.xnf", "../../benchmarks/instances/2xnfs/rand/rand-10-20.xnf", "../../benchmarks/instances/2xnfs/rand/rand-20-40.xnf");
    //auto fname = "../../benchmarks/instances/2xnfs/rand/rand-20-40.xnf";
    //auto fname = "../../benchmarks/instances/2xnfs/rand/rand-10-20.xnf";
    //auto fname = "../../benchmarks/instances/2xnfs/rand/rand-3-6.xnf";
    //auto fname = "../../benchmarks/instances/2xnfs/mq/toyexamples/ToyExample-type1-n10-seed0.xnf";
    auto clss = parse_file( fname );
    auto xnf = clss.cls;
    var_t num_vars = clss.num_vars;
    dec_heu dh = GENERATE(dec_heu::vsids, dec_heu::lex);
    phase_opt po = GENERATE(phase_opt::rand, phase_opt::save, phase_opt::save_inv);
    ca_alg ca = ca_alg::no; //GENERATE(ca_alg::no, ca_alg::fuip);
    int la_sch = 10; //GENERATE(0,1,10);
    options opts(dh, po, ca, la_sch, 0, 0);

    stats s = solve(xnf, num_vars, opts);
    CHECK( s.sat == true ); //SAT
    CHECK( check_sols(clss.cls, s.sols) );
}


TEST_CASE( "solving within timeout" , "[parser][solve]" ) {
    auto fname = GENERATE("../../benchmarks/instances/2xnfs/mq/toyexamples/ToyExample-type1-n10-seed0.xnf", "../../benchmarks/instances/2xnfs/rand/rand-3-6.xnf", "../../benchmarks/instances/2xnfs/rand/rand-10-20.xnf", "../../benchmarks/instances/2xnfs/rand/rand-20-40.xnf");
    //auto fname = "../../benchmarks/instances/2xnfs/rand/rand-20-40.xnf";
    //auto fname = "../../benchmarks/instances/2xnfs/rand/rand-10-20.xnf";
    //auto fname = "../../benchmarks/instances/2xnfs/rand/rand-3-6.xnf";
    //auto fname = "../../benchmarks/instances/2xnfs/mq/toyexamples/ToyExample-type1-n10-seed0.xnf";
    auto clss = parse_file( fname );
    auto xnf = clss.cls;
    auto num_vars = clss.num_vars;

    options opts(dec_heu::vsids, phase_opt::save, ca_alg::fuip, 100, 0, 0);
    std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
    stats s = solve(xnf, num_vars, opts);
    std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
    float time_no_time_out = static_cast<float>(std::chrono::duration_cast<std::chrono::milliseconds>(end - begin).count())/1000.0f;

    options opts2(dec_heu::vsids, phase_opt::save, ca_alg::fuip, 100, 0, time_no_time_out+3);
    begin = std::chrono::steady_clock::now();
    stats s2 = solve(xnf, num_vars, opts2);
    end = std::chrono::steady_clock::now();
    float time_with_time_out = static_cast<float>(std::chrono::duration_cast<std::chrono::milliseconds>(end - begin).count())/1000.0f;
  #ifdef NDEBUG
    CHECK( time_no_time_out == Catch::Approx(time_with_time_out).margin(0.1) );
  #else
    CHECK( time_no_time_out == Catch::Approx(time_with_time_out).margin(0.5) );
  #endif
    CHECK( s.finished == true ); //SAT
    CHECK( s.sat == true ); //SAT
    CHECK( check_sols(clss.cls, s.sols) );
}

TEST_CASE("solving with different options -- timeout", "[parser][solve]")  {
  #ifdef NDEBUG
    auto clss = parse_file("../../benchmarks/instances/2xnfs/mq/challenge-1-55-0.xnf");
  #else
    auto clss = parse_file("../../benchmarks/instances/2xnfs/mq/toyexamples/ToyExample-type1-n20-seed0.xnf");
  #endif
    auto xnf = clss.cls;
    auto num_vars = clss.num_vars;

    options opts(dec_heu::vsids, phase_opt::save, ca_alg::fuip, 50, 0, 1);
    stats s = solve(xnf, num_vars, opts);

    CHECK( s.finished == false );
}