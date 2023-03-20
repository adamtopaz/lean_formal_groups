import tactic
import ring_theory.ideal.quotient
import ring_theory.power_series.basic
import ring_theory.polynomial.basic

noncomputable theory
open_locale classical
open_locale big_operators


variables (σ τ ω R : Type*) [comm_ring R]

namespace mv_power_series

def variable_ideal : ideal (mv_power_series σ R) :=
ideal.span (set.range mv_power_series.X)

noncomputable def degree_geq : ℕ → ideal (mv_power_series σ R) 
| 0 := ⊤
| (n+1) := degree_geq n * variable_ideal σ R

variables {σ τ ω R}
def congruent_mod (n : ℕ) (F G : mv_power_series σ R) : Prop :=
F - G ∈ degree_geq σ R n


open finset

variables {σ τ ω R}
def nth_pow (n : ℕ) (F : mv_power_series σ R) : mv_power_series σ R := (∏ i in range n, F)


def incl_fun : mv_power_series σ R → mv_power_series (σ ⊕ τ) R := 
  show ((σ →₀ ℕ) → R) → ((σ ⊕ τ →₀ ℕ) → R), from λ f m, 
  let n := finsupp.sum_finsupp_equiv_prod_finsupp m in
  if n.2 = 0 then f n.1 else 0

#check mv_polynomial.eval₂_hom 
-- mv_polynomial.C or.inl
/--begin
  ext m,
  unfold incl_fun,
  rw coeff_one,
  split_ifs,
  end,-/
def incl : mv_power_series σ R →+* mv_power_series (σ ⊕ τ) R :=
{ to_fun := incl_fun,
  map_one' :=  begin
  ext n,
  unfold incl_fun,
  rw coeff_one,
  simp,
  split_ifs,
  end,
  map_mul' := begin
  intros F G,
  ext,
  unfold incl_fun,
  simp,
  rw coeff_mul,
  end,
  map_zero' := begin
  ext,
  unfold incl_fun,
  simp,
  refl,
  end,
  map_add' := sorry }

def incr_fun : mv_power_series τ R → mv_power_series (σ ⊕ τ) R := 
  show ((τ →₀ ℕ) → R) → ((σ ⊕ τ →₀ ℕ) → R), from λ f m, 
  let n := finsupp.sum_finsupp_equiv_prod_finsupp m in
  if n.1 = 0 then f n.2 else 0

def incr : mv_power_series τ R →+* mv_power_series (σ ⊕ τ) R :=
{ to_fun := incr_fun,
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }


def change_var (e : σ ≃ τ) : mv_power_series σ R ≃+* mv_power_series τ R := 
sorry

def compose 
  (F : mv_power_series σ R) -- F(X_1,X_2,...,X_n) 
  (G : σ → mv_power_series τ R) -- G_1(X_1,...,X_m), ..., G_n(X_1,...,X_m)
  (hG : ∀ i, congruent_mod 1 (G i) 0) :
  mv_power_series τ R := λ (n : τ →₀ ℕ ), --(n : (τ →₀ ℕ) => ) -- F(G_1(X_1,...,X_m),...,G_n(X_1,...,X_m))

def compose_fst 
  (F : mv_power_series (σ ⊕ τ) R) -- F(X_1,...,X_n;Y_1,...,Y_m)
  (G : σ → mv_power_series ω R) -- G_1(Z_1,...,Z_k), ..., G_n(Z_1,...,Z_k)
  (hG : ∀ i, congruent_mod 1 (G i) 0) :
  mv_power_series (ω ⊕ τ) R := -- F(G_1(Z_1,...,Z_k),...,G_n(Z_1,...,Z_k);Y_1,...,Y_m)
sorry 

def compose_snd 
  (F : mv_power_series (σ ⊕ τ) R) -- F(X_1,...,X_n;Y_1,...,Y_m)
  (G : τ → mv_power_series ω R) -- G_1(Z_1,...,Z_k), ..., G_m(Z_1,...,Z_k)
  (hG : ∀ i, congruent_mod 1 (G i) 0) :
  mv_power_series (σ ⊕ ω) R := -- F(X_1,...,X_n;G_1(Z_1,...,Z_k),...,G_m(Z_1,...,Z_k))
sorry 


end mv_power_series

structure mv_formal_group_law :=
(F : σ → mv_power_series (σ ⊕ σ) R)
(F_mod_2 : ∀ i, mv_power_series.congruent_mod 2 (F i) 
  (mv_power_series.X (sum.inl i) + mv_power_series.X (sum.inr i)))
(F_assoc : ∀ i, 
  mv_power_series.compose_snd (F i) F sorry  -- should follow from F_mod_2
  = 
  mv_power_series.change_var (equiv.sum_assoc _ _ _)
  (mv_power_series.compose_fst (F i) F sorry))
  