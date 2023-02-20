# p-adic-L-functions

This project formalizes p-adic L-functions in Lean 3. We define p-adic L-function in terms of p-adic integrals with respect to the Bernoulli measure. We also prove that the p-adic L-functions evaluated at negative integers give values of generalized Bernoulli numbers twisted by Dirichlet and Teichmuller characters. All of these are formalized in this repository.

Installation instructions
To install Lean 3, look at https://leanprover-community.github.io/get_started.html. After installation, one may use the command leanproject get laughinggas/p-adic-L-functions to obtain a local copy of the relevant source files and all dependencies.

Code overview
The following files contain major contributions from our project:

[src/neg_int_eval.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/neg_int_eval.lean}
[src/p_adic_L_function_def.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/p_adic_L_function_def.lean}
[src/padic_integral.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/padic_integral.lean}
[src/general_bernoulli_number/lim_even_character_of_units.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/general_bernoulli_number/lim_even_character_of_units.lean}
[src/bernoulli_measure/bernoulli_measure_def.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/bernoulli_measure/bernoulli_measure_def.lean}

We provide an overview of the source code files containing results mentioned in the paper.
Section 3
Dirichlet characters basic properties: [src/dirichlet_character/basic.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/dirichlet_character/basic.lean}
Casting Dirichlet characters: [src/dirichlet_character/dvd_mul_conductor.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/dirichlet_character/dvd_mul_conductor.lean}
Teichmüller character: [src/dirichlet_character/teichmuller_character.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/dirichlet_character/teichmuller_character.lean}
Section 4
Generalized Bernoulli numbers: [src/general_bernoulli_number/basic.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/general_bernoulli_number/basic.lean}
Theorem 1: [src/general_bernoulli_number/lim_even_character.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/general_bernoulli_number/lim_even_character.lean}
Theorem 2: [src/tendsto_zero_of_sum_even_char.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/tendsto_zero_of_sum_even_char.lean}
Section 5
Clopen basis of p-adic integers: [src/padic_int/clopen_properties.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/padic_int/clopen_properties.lean}
p-adic measures: [src/padic_integral.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/padic_integral.lean}
Bernoulli distribution: [src/bernoulli_measure/bernoulli_distribution.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/bernoulli_measure/bernoulli_distribution.lean}
Bernoulli measure: [src/bernoulli_measure/bernoulli_measure_def.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/bernoulli_measure/bernoulli_measure_def.lean}
Eventually constant sequences: [src/bernoulli_measure/eventually_constant_sequence.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/bernoulli_measure/eventually_constant_sequence.lean}
`from_loc_const`: [src/bernoulli_measure/from_loc_const.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/bernoulli_measure/from_loc_const.lean}
Locally constant functions: [src/bernoulli_measure/loc_const_properties.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/bernoulli_measure/loc_const_properties.lean}
A discrete quotient: [src/padic_int/clopen_properties.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/padic_int/clopen_properties.lean}
`equi_class` and `zmod'`: src/bernoulli_measure/equi_class.lean
Sums regarding Bernoulli distribution: [src/bernoulli_measure/equi_class.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/bernoulli_measure/equi_class.lean}
p-adic integral: [src/padic_integral.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/padic_integral.lean}
p-adic L-function: [src/p_adic_L_function_def.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/p_adic_L_function_def.lean}
Section 6
Factors of the conductor: [src/dirichlet_character/dvd_mul_conductor.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/dirichlet_character/dvd_mul_conductor.lean}
Evaluation at negative integers: [src/neg_int_eval.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/neg_int_eval.lean}
First sum: [src/general_bernoulli_number/lim_even_character_of_units.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/general_bernoulli_number/lim_even_character_of_units.lean}
Second sum: [src/sum_eval/second_sum.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/sum_eval/second_sum.lean}
Third sum: [src/sum_eval/third_sum.lean]{https://github.com/laughinggas/p-adic-L-functions/blob/main/src/sum_eval/third_sum.lean}
