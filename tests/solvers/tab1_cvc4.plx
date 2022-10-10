#!/usr/bin/perl

@files = <../smt2/quad-*.smt2>;



foreach $file (@files) {
    print "\n" .$file . "\n";

    system("./cvc4_run.sh " . $file );

}

