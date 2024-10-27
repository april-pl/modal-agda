mkdir lagda

function agda_latex {
    cd $1
    for f in src/*.agda; do
        agda --latex --only-scope-checking $f
    done
    cd ..
}

function take_latex {
    mv $1/latex lagda/$1
}

function do_it {
    agda_latex $1
    take_latex $1
}

do_it fitch
do_it moggi
