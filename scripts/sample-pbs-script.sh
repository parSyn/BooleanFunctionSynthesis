#PBS -l nodes=4:ppn=5
#PBS -l vmem=16gb
#PBS -l walltime=1:00:00
#PBS -q batch
#PBS -V
# Set Intel MPI environment
#mpi_dir=/usr/mpi/gcc/openmpi-1.8.2rc6/bin/
#source $mpi_dir/mpivars.sh

# Go to the present directory
cd $HOME/path_to_experiments_directory/

# Set paths of mpiexec and parSK in the PATH variable 
export PATH=$HOME/path_to_openmpi_bin/:$HOME/path_to_parSK_bin/:$PATH 

# Launch application
(time mpiexec -np 20 parSK bobsm5378d2_all_bit_differing_from_cycle.v bobsm5378d2_all_bit_differing_from_cycle_arbitraryboolean_least_occurring_first_order.txt 2 bobsm5378d2_all_bit_differing_from_cycle_arbitraryboolean_least_occurring_first_order.txt 0 1 0) 
