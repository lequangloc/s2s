#!/usr/bin/perl

@files = <../flat/quad-*>;



foreach $file (@files) {
    print "\n" .$file . "\n";

    system("./s2str_run.sh " . $file );

}

