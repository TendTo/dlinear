#!/bin/bash
# Example SLURM job script for serial (non-parallel) jobs
#
# SLURM defaults to the directory you were working in when you submitted the job.
# Output files are also put in this directory. To set a different working directory add:
#
##SBATCH –-workdir=/mnt/nfs/home/c3054737/dlinear4
#
#SBATCH --time=12:00:00
#
# Tell SLURM if you want to be emailed when your job starts, ends, etc.
#
##SBATCH --mail-type=ALL
#
# set up a job array with tasks numbered 1 to 100.
#SBATCH --array=0-1247
#
# Type of nodes to use: 
# defq          standard        528 cores   2 days      2 days      2.5 GB
# bigmem        medium,large,XL 2 nodes     2 days(*)   2 days      11 GB
# short         all             2 nodes     10 minutes  1 minute    2.5 GB
# long          standard        2 nodes     30 days     5 days      2.5 GB
# power(**)     power           1 node      2 days      2 days      2.5 GB
# interactive   all             1 node      1 day       2 hours     2.5 GB
#SBATCH --partition=defq
#
# request one core per task
#SBATCH -c 1
#
# give the array a single job name
#SBATCH -J dlinear-benchmark-smt-complete
#
# Use custom files for both stdout and stderr
#
#SBATCH -o job/job_%A_%a.out
#SBATCH -e job/job_%A_%a.err
#
shopt -s nullglob
dir="smt2"
type="smt2"
output_dir="lp_results"

# Create an array with all the files in the mps direcory.
# They are also sorted to ensure reproducibility
input_files=($dir/*.$type)
IFS=$'\n' input_files=($(sort <<<"${input_files[*]}"))
unset IFS

function run() {
    file="${input_files[$1]}"
    filename=$(basename "$file")
    filename="${filename%.*}"

    ./dlinear "$file" -t -p 0 --csv --bound-implication-frequency never --bound-propagation-frequency never --disable-expansion > "$output_dir/$filename.dlinear.0.stats"
}

if [[ -z $SLURM_ARRAY_TASK_ID ]]; then
    for i in {0..1248}
    do
        run $i
    done
else
    run $SLURM_ARRAY_TASK_ID
fi    
