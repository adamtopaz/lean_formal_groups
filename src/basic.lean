import tactic
import ring_theory.ideal.quotient
import ring_theory.power_series.basic
import ring_theory.polynomial.basic

noncomputable theory
open_locale classical
open_locale big_operators


variables (σ τ ω R : Type*) [comm_ring R]

namespace mv_power_series

#check mv_polynomial.eval₂

variables {σ τ}

@[simp]
lemma incl_monomial_aux (ι : σ ↪ τ) (m : σ →₀ ℕ) (t : σ) : 
  m.map_domain ι (ι t) = m t := 
begin
  sorry -- see commented proof below
end

def incl_monomial (ι : σ ↪ τ) : (σ →₀ ℕ) ↪ (τ →₀ ℕ) := 
{ to_fun := λ m, finsupp.map_domain ι m,
  inj' := begin
    intros m1 m2 h,
    dsimp at h,
    ext t,
    apply_fun (λ e, e (ι t)) at h,
    simpa only [incl_monomial_aux] using h,
    /-
    have h1 : m1 t = m1.map_domain ι (ι t), by simp only [incl_monomial_aux],
    /-
    { dsimp [finsupp.map_domain],
      simp,
      -- TODO: Take a look at the docs for `finsupp.sum`.
      have : m1 t = m1.sum (λ a n, if a = t then n else 0),
      { simp },
      convert this using 2,
      ext a b,
      rw finsupp.single_apply,
      rw (ι.injective.eq_iff : ι a = ι t ↔ a = t) },
    -/
    have h2 : m2 t = m2.map_domain ι (ι t), sorry, -- similar to above. (extract a helper lemma).
    simp [h1, h2, h]
    -/
  end }

def incl_fun (ι : σ ↪ τ) : mv_power_series σ R → mv_power_series τ R := 
λ f m, if h : ∃ m' : σ →₀ ℕ, incl_monomial ι m' = m then f h.some else 0

@[simp]
lemma constant_coeff_incl (ι : σ ↪ τ) (f : mv_power_series σ R) : 
  constant_coeff τ R (incl_fun R ι f) = constant_coeff σ R f := 
sorry

lemma incl_one (ι : σ ↪ τ) : 
  incl_fun R ι 1 = 1 :=
begin
  ext m,
  simp only [mv_power_series.coeff_one],
  split_ifs,
  { simp [h] },
  { dsimp [incl_fun, coeff], split_ifs with hh hh,
    { let m' := hh.some,
      have h' : m' ≠ 0, sorry,
      change (coeff R m') 1 = 0,
      rw mv_power_series.coeff_one,
      rw if_neg h' },
    { refl } }
end

def incl (ι : σ ↪ τ) : mv_power_series σ R →+* mv_power_series τ R := 
{ to_fun := incl_fun _ ι,
  map_one' := incl_one _ _,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }

variable (σ)
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
  