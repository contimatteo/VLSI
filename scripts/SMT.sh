#!/bin/bash

trap break INT

#

instances=(
    "ins-1" "ins-2" "ins-3" "ins-4" "ins-5" "ins-6" "ins-7" "ins-8" "ins-9" "ins-10" 
    "ins-11" "ins-12" "ins-13" "ins-14" "ins-15" "ins-16" "ins-17" "ins-18" "ins-19" "ins-20" 
    "ins-21" "ins-22" "ins-23" "ins-24" "ins-25" "ins-26" "ins-27" "ins-28" "ins-29" "ins-30" 
    "ins-31" "ins-32" "ins-33" "ins-34" "ins-35" "ins-36" "ins-37" "ins-38" "ins-39" "ins-40"
)

#

SMT(){
    python src/SMT.py --model $1 --data $2 --search "linear" 2>/dev/null
  
    python src/SMT.py --model $1 --data $2 --search "linear" --symmetry 2>/dev/null

    python src/SMT.py --model $1 --data $2 --search "linear" --cumulative 2>/dev/null

    python src/SMT.py --model $1 --data $2 --search "linear" --symmetry --cumulative 2>/dev/null
}

#

for data in "${instances[@]}"
do
    SMT "base" $data
    SMT "rotation" $data
    echo "$data"
done
