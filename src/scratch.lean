import topology.algebra.nonarchimedean.bases
import norm_properties

open_locale big_operators

example {A : Type*} [topological_space A] [ring A] [nonarchimedean_ring A] : topological_space A := infer_instance

structure nonarch {A : Type*} [uniform_space A] := 
(B : filter_basis A) 
(is_nonarch : ∀ P ∈ B, ∀x y (h : (x, y) ∈ P), (y, x) ∈ P )
(h : uniformity A = filter_basis.filter B)       
--∧ (uniformity A). (λ (s : set A), _)) _

example {A ι : Type*} [normed_ring A] [nonempty ι] {B : ι → add_subgroup A} (hB : ring_subgroups_basis B) (f : ℕ → A) (a b : ℕ) :
  ∥(f a + f b)∥ ≤ (max ∥f a∥ ∥f b∥) := 
begin
  rw nonarchimedean_add_group,
  have := @normed_group.uniformity_basis_dist A _,    
  rw filter.principal,    
  rw le_max_iff,
  have := @topological_space_eq_iff A infer_instance hB.topology,
  --wlog h : ∥f a∥ ≤ ∥f b∥ using [a b, b a],
   
  have := uniform_space.to_core_to_topological_space,
  sorry
end

example {R : Type*} [normed_comm_ring R] [nonarchimedean_ring R] : 
(∀ (n : ℕ) (f : ℕ → R), ∥∑ (i : ℕ) in finset.range n, f i∥ ≤ (⨆ (i : zmod n), ∥f i.val∥)) ∧ 
  ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥ := 
begin
  split,
  { intros n f,
    induction n with d hd,
    { simp only [finset.range_zero, finset.sum_empty, norm_zero],
      sorry, },
    { simp_rw finset.sum_range_succ,
      sorry, }, },
  sorry
end

open filter
def g {R : Type*} (f : ℕ → R) := λ n : ℕ, (λ i : finset.range n, f i)

example {R : Type*} [normed_comm_ring R] [nonarchimedean_ring R] (k : R) 
  (f : ℕ → R) (h : tendsto (λ n : ℕ, set.image f (finset.range n)) at_top (nhds {k})) : 
  tendsto (λ n, ∑ (i : ℕ) in finset.range n, f i) at_top (nhds k) := 
begin
  rw tendsto_def at *,
  intros s hs,
  simp only [mem_at_top_sets, ge_iff_le, set.mem_preimage] at *,
  rw uniform_space,
  sorry
end