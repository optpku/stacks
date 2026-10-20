module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Length-two polynomial terms of an algebra presentation

The polynomial carriers `P0`, `P1`, `P2`, the syzygy module
`Rel`, the generators `x_t`, `y_t`, `z_t`, `v_r`, `w_{t,t'}`, and the face
and degeneracy maps describe a polynomial construction through degree two.
-/

public section

open Algebra
open MvPolynomial

universe u

namespace Algebra.Presentation.LengthTwo

variable {A B ι σ : Type u} [CommRing A] [CommRing B] [Algebra A B]

noncomputable section

/-- The module of syzygies among the chosen relations `f_t`. -/
@[expose]
abbrev Rel (P : Presentation A B ι σ) : Submodule P.Ring (σ →₀ P.Ring) :=
  LinearMap.ker (Finsupp.linearCombination P.Ring P.relation)

/-- Membership in `Rel` is vanishing of the linear combination `∑ r_t f_t`. -/
theorem Rel.mem_iff {P : Presentation A B ι σ} {r : σ →₀ P.Ring} :
    r ∈ Rel P ↔ Finsupp.linearCombination P.Ring P.relation r = 0 :=
  sorry

/-- The defining linear combination of a syzygy is zero. -/
theorem Rel.linearCombination_eq_zero {P : Presentation A B ι σ} (r : Rel P) :
    Finsupp.linearCombination P.Ring P.relation r.1 = 0 :=
  sorry

/-- Variables of the length-two polynomial algebra `P2 = A[u_i, y_t, z_t, v_r, w_{t,t'}]`. -/
inductive Vars (P : Presentation A B ι σ) : Type u where
  | u (i : ι) : Vars P
  | y (t : σ) : Vars P
  | z (t : σ) : Vars P
  | v (r : Rel P) : Vars P
  | w (t t' : σ) : Vars P

/-- The degree-zero polynomial algebra `P0 = A[u_i]`. -/
@[expose]
abbrev term0 (P : Presentation A B ι σ) := P.Ring

/-- Unfolding `term0` recovers the polynomial ring of the presentation. -/
theorem term0_eq (P : Presentation A B ι σ) : term0 P = P.Ring :=
  sorry

/-- The degree-one polynomial algebra `P1 = A[u_i, x_t]`. -/
@[expose]
abbrev term1 (P : Presentation A B ι σ) := MvPolynomial (ι ⊕ σ) A

/-- The degree-two polynomial algebra `P2 = A[u_i, y_t, z_t, v_r, w_{t,t'}]`. -/
@[expose]
abbrev term2 (P : Presentation A B ι σ) := MvPolynomial (Vars P) A

/-- The generator `x_t` of `P1`. -/
@[expose]
def x (P : Presentation A B ι σ) (t : σ) : term1 P :=
  X (Sum.inr t)

/-- Unfolding `x` recovers the multivariate indeterminate on the relation index. -/
theorem x_def (P : Presentation A B ι σ) (t : σ) :
    x P t = X (Sum.inr t) :=
  sorry

/-- The face `d0 : P1 → P0` with `d0(u_i) = u_i` and `d0(x_t) = 0`. -/
@[expose]
def faceZero (P : Presentation A B ι σ) : term1 P →ₐ[A] P.Ring :=
  aeval (Sum.elim X (fun _ ↦ 0))

/-- The face `d1 : P1 → P0` with `d1(u_i) = u_i` and `d1(x_t) = f_t`. -/
@[expose]
def faceOne (P : Presentation A B ι σ) : term1 P →ₐ[A] P.Ring :=
  aeval (Sum.elim X P.relation)

/-- The degeneracy `s0 : P0 → P1` with `s0(u_i) = u_i`. -/
@[expose]
def degeneracyZero (P : Presentation A B ι σ) : P.Ring →ₐ[A] term1 P :=
  rename Sum.inl

/-- `d0` fixes the original generators `u_i`. -/
theorem faceZero_X (P : Presentation A B ι σ) (i : ι) :
    faceZero P (X (Sum.inl i)) = X i :=
  sorry

/-- `d0` sends `x_t` to `0`. -/
theorem faceZero_x (P : Presentation A B ι σ) (t : σ) :
    faceZero P (x P t) = 0 :=
  sorry

/-- `d1` fixes the original generators `u_i`. -/
theorem faceOne_X (P : Presentation A B ι σ) (i : ι) :
    faceOne P (X (Sum.inl i)) = X i :=
  sorry

/-- `d1` sends `x_t` to the relation `f_t`. -/
theorem faceOne_x (P : Presentation A B ι σ) (t : σ) :
    faceOne P (x P t) = P.relation t :=
  sorry

/-- `s0` sends `u_i` to the same generator of `P1`. -/
theorem degeneracyZero_X (P : Presentation A B ι σ) (i : ι) :
    degeneracyZero P (X i) = X (Sum.inl i) :=
  sorry

/-- The identity `d0 ∘ s0 = id` on `P0`. -/
theorem faceZero_comp_degeneracyZero (P : Presentation A B ι σ) :
    (faceZero P).comp (degeneracyZero P) = AlgHom.id A P.Ring :=
  sorry

/-- The identity `d1 ∘ s0 = id` on `P0`. -/
theorem faceOne_comp_degeneracyZero (P : Presentation A B ι σ) :
    (faceOne P).comp (degeneracyZero P) = AlgHom.id A P.Ring :=
  sorry

/-- The matching triple `y_t = (x_t, x_t, f_t)`. -/
@[expose]
def y (P : Presentation A B ι σ) (t : σ) : term1 P × term1 P × term1 P :=
  (x P t, x P t, degeneracyZero P (P.relation t))

/-- The first coordinate of `y_t` is `x_t`. -/
theorem y_fst (P : Presentation A B ι σ) (t : σ) :
    (y P t).1 = x P t :=
  sorry

/-- The second coordinate of `y_t` is `x_t`. -/
theorem y_snd_left (P : Presentation A B ι σ) (t : σ) :
    (y P t).2.1 = x P t :=
  sorry

/-- The third coordinate of `y_t` is the degeneracy of `f_t`. -/
theorem y_snd (P : Presentation A B ι σ) (t : σ) :
    (y P t).2.2 = degeneracyZero P (P.relation t) :=
  sorry

/-- The matching triple `z_t = (0, x_t, x_t)`. -/
@[expose]
def z (P : Presentation A B ι σ) (t : σ) : term1 P × term1 P × term1 P :=
  (0, x P t, x P t)

/-- The first coordinate of `z_t` is `0`. -/
theorem z_fst (P : Presentation A B ι σ) (t : σ) :
    (z P t).1 = 0 :=
  sorry

/-- The second coordinate of `z_t` is `x_t`. -/
theorem z_snd_left (P : Presentation A B ι σ) (t : σ) :
    (z P t).2.1 = x P t :=
  sorry

/-- The third coordinate of `z_t` is `x_t`. -/
theorem z_snd (P : Presentation A B ι σ) (t : σ) :
    (z P t).2.2 = x P t :=
  sorry

/-- The third matching coordinate `∑ r_t x_t` of a syzygy `r ∈ Rel`. -/
@[expose]
def v (P : Presentation A B ι σ) (r : Rel P) : term1 P :=
  Finsupp.linearCombination (term1 P) (fun t : σ ↦ x P t)
    (r.1.mapRange (degeneracyZero P : P.Ring → term1 P) (map_zero (degeneracyZero P)))

/-- `v_r` is the image of the coefficient family of `r` under `∑ r_t x_t`. -/
theorem v_eq_sum (P : Presentation A B ι σ) (r : Rel P) :
    v P r =
      r.1.sum (fun t coeff ↦ degeneracyZero P coeff * x P t) :=
  sorry

/-- The third matching coordinate `x_t x_{t'} - f_t x_{t'}`. -/
@[expose]
def w (P : Presentation A B ι σ) (t t' : σ) : term1 P :=
  x P t * x P t' - degeneracyZero P (P.relation t) * x P t'

/-- Unfolding `w` recovers the quadratic syzygy in `x_t`. -/
theorem w_def (P : Presentation A B ι σ) (t t' : σ) :
    w P t t' = x P t * x P t' - degeneracyZero P (P.relation t) * x P t' :=
  sorry

/-- The assignment of `P2`-generators determining `d_i : P2 → P1`. -/
private def faceTwoVal (P : Presentation A B ι σ) (i : Fin 3) : Vars P → term1 P
  | .u a => X (Sum.inl a)
  | .y t => if i = 2 then degeneracyZero P (P.relation t) else x P t
  | .z t => if i = 0 then 0 else x P t
  | .v r => if i = 2 then v P r else 0
  | .w t t' => if i = 2 then w P t t' else 0

/-- The faces `d0, d1, d2 : P2 → P1` determined by the matching assignment. -/
def faceTwo (P : Presentation A B ι σ) (i : Fin 3) : term2 P →ₐ[A] term1 P :=
  aeval (faceTwoVal P i)

/-- `d_i` sends `u_a` to the same generator of `P1`. -/
theorem faceTwo_u (P : Presentation A B ι σ) (i : Fin 3) (a : ι) :
    faceTwo P i (X (.u a)) = X (Sum.inl a) :=
  sorry

/-- `d0` and `d1` send `y_t` to `x_t`, while `d2` sends `y_t` to `f_t`. -/
theorem faceTwo_y (P : Presentation A B ι σ) (i : Fin 3) (t : σ) :
    faceTwo P i (X (.y t)) = if i = 2 then degeneracyZero P (P.relation t) else x P t :=
  sorry

/-- `d0` sends `z_t` to `0`, while `d1` and `d2` send `z_t` to `x_t`. -/
theorem faceTwo_z (P : Presentation A B ι σ) (i : Fin 3) (t : σ) :
    faceTwo P i (X (.z t)) = if i = 0 then 0 else x P t :=
  sorry

/-- `d0` and `d1` send `v_r` to `0`, while `d2` sends `v_r` to `∑ r_t x_t`. -/
theorem faceTwo_v (P : Presentation A B ι σ) (i : Fin 3) (r : Rel P) :
    faceTwo P i (X (.v r)) = if i = 2 then v P r else 0 :=
  sorry

/-- `d0` and `d1` send `w_{t,t'}` to `0`, while `d2` sends it to `x_t x_{t'} - f_t x_{t'}`. -/
theorem faceTwo_w (P : Presentation A B ι σ) (i : Fin 3) (t t' : σ) :
    faceTwo P i (X (.w t t')) = if i = 2 then w P t t' else 0 :=
  sorry

/-- The degeneracies `s0, s1 : P1 → P2` with `s0(x_t) = y_t` and `s1(x_t) = z_t`. -/
@[expose]
def degeneracyOne (P : Presentation A B ι σ) (j : Fin 2) : term1 P →ₐ[A] term2 P :=
  aeval (Sum.elim (fun a ↦ X (.u a))
    (fun t ↦ if j = 0 then X (.y t) else X (.z t)))

/-- `s_j` sends `u_i` to the same generator of `P2`. -/
theorem degeneracyOne_X (P : Presentation A B ι σ) (j : Fin 2) (i : ι) :
    degeneracyOne P j (X (Sum.inl i)) = X (.u i) :=
  sorry

/-- `s0(x_t) = y_t` and `s1(x_t) = z_t`. -/
theorem degeneracyOne_x (P : Presentation A B ι σ) (j : Fin 2) (t : σ) :
    degeneracyOne P j (x P t) = if j = 0 then X (.y t) else X (.z t) :=
  sorry

namespace Triple

/-- Compatibility of a triple `(g0, g1, g2)` in `P1^3` for the degree-two matching
object of the `1`-truncated object: `d0(g0) = d0(g1)`, `d1(g0) = d0(g2)`, and
`d1(g1) = d1(g2)`. -/
@[expose]
def Compatible (P : Presentation A B ι σ) (g0 g1 g2 : term1 P) : Prop :=
  faceZero P g0 = faceZero P g1 ∧
    faceOne P g0 = faceZero P g2 ∧
    faceOne P g1 = faceOne P g2

/-- Unfolding `Compatible` recovers the three face equalities of `cosk1(P)_2`. -/
theorem compatible_iff (P : Presentation A B ι σ) (g0 g1 g2 : term1 P) :
    Compatible P g0 g1 g2 ↔
      faceZero P g0 = faceZero P g1 ∧
        faceOne P g0 = faceZero P g2 ∧
        faceOne P g1 = faceOne P g2 :=
  sorry

/-- The triple `y_t` lies in the degree-two matching object. -/
theorem compatible_y (P : Presentation A B ι σ) (t : σ) :
    Compatible P (y P t).1 (y P t).2.1 (y P t).2.2 :=
  sorry

/-- The triple `z_t` lies in the degree-two matching object. -/
theorem compatible_z (P : Presentation A B ι σ) (t : σ) :
    Compatible P (z P t).1 (z P t).2.1 (z P t).2.2 :=
  sorry

/-- The triple `(0, 0, v_r)` lies in the degree-two matching object. -/
theorem compatible_v (P : Presentation A B ι σ) (r : Rel P) :
    Compatible P 0 0 (v P r) :=
  sorry

/-- The triple `(0, 0, w_{t,t'})` lies in the degree-two matching object. -/
theorem compatible_w (P : Presentation A B ι σ) (t t' : σ) :
    Compatible P 0 0 (w P t t') :=
  sorry

/-- The image of a degree-two polynomial under `(d0, d1, d2)` is a matching triple. -/
theorem compatible_faceTwo (P : Presentation A B ι σ) (p : term2 P) :
    Compatible P (faceTwo P 0 p) (faceTwo P 1 p) (faceTwo P 2 p) :=
  sorry

end Triple

/-- The joint face map `(d0, d1) : P1 → P0 × P0`. -/
@[expose]
def toProd (P : Presentation A B ι σ) : term1 P →ₐ[A] P.Ring × P.Ring :=
  AlgHom.prod (faceZero P) (faceOne P)

/-- `toProd` is componentwise `d0` and `d1`. -/
theorem toProd_apply (P : Presentation A B ι σ) (p : term1 P) :
    toProd P p = (faceZero P p, faceOne P p) :=
  sorry

/-- The two components of `toProd` become equal after composing to `B`. -/
theorem toProd_comp_aeval (P : Presentation A B ι σ) (p : term1 P) :
    aeval P.val (faceZero P p) = aeval P.val (faceOne P p) :=
  sorry

end

end Algebra.Presentation.LengthTwo
