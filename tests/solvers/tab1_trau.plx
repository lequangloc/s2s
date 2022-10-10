#!/usr/bin/perl

@files = <../../trau/quad-*.smt2>;



foreach $file (@files) {
    print "\n" .$file . "\n";

    system("./trau_run.sh " . $file );

}

