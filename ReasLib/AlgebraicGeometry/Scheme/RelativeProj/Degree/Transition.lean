module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.Quadruple
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Power

/-!
# Canonical changes of degree for relative projective quadruples

For `e = a * d`, keep the structure morphism, take the `a`th tensor power of
the line bundle, and restrict the graded map to the `e`th Veronese pieces.
The maps use the existing recursive tensor-power comparison, not a chosen
comparison isomorphism.
-/

@[expose] public section

open CategoryTheory Opposite SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeProjDegreeQuadruple

variable {S T : Scheme.{u}} {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf} {d : ℕ}

/-- Restriction of the graded map to degrees divisible by `a * d`, followed by
the canonical rebracketing into powers of `L^a`. -/
def powerPsi (q : RelativeProjDegreeQuadruple 𝒜 d T) (a n : ℕ) :
    𝒜 (Int.ofNat (n * (a * d))) ⟶
      (Scheme.Modules.pushforward q.morphism).obj
        (RingedSpace.TensorPower.sheaf
          (RingedSpace.TensorPower.sheaf q.lineBundle a) n) :=
  eqToHom (congrArg (fun k : ℕ ↦ 𝒜 (Int.ofNat k)) (Nat.mul_assoc n a d).symm) ≫
    q.psi (n * a) ≫
      (Scheme.Modules.pushforward q.morphism).map
        (RingedSpace.TensorPower.mulIso q.lineBundle a n).inv

/-- The degree-one map of the restricted Veronese family is its actual adjoint. -/
def powerDegreeOneMap (q : RelativeProjDegreeQuadruple 𝒜 d T) (a : ℕ) :
    (Scheme.Modules.pullback q.morphism).obj (𝒜 (Int.ofNat (1 * (a * d)))) ⟶
      RingedSpace.TensorPower.sheaf
        (RingedSpace.TensorPower.sheaf q.lineBundle a) 1 :=
  ((Scheme.Modules.pullbackPushforwardAdjunction q.morphism).homEquiv
    (𝒜 (Int.ofNat (1 * (a * d))))
    (RingedSpace.TensorPower.sheaf
      (RingedSpace.TensorPower.sheaf q.lineBundle a) 1)).symm (powerPsi q a 1)

/-- Multiplicativity and the original degree-one epimorphism imply that the
restricted positive-degree map onto the corresponding tensor power is epi. -/
theorem powerDegreeOneMap_epi (q : RelativeProjDegreeQuadruple 𝒜 d T)
    (a : ℕ) (ha : 1 ≤ a) : Epi (powerDegreeOneMap q a) := sorry

/-- The canonical degree multiplication `(d,f,L,ψ) ↦ (a*d,f,L^a,ψ|)`. -/
def power (q : RelativeProjDegreeQuadruple 𝒜 d T) (a : ℕ) (ha : 1 ≤ a) :
    RelativeProjDegreeQuadruple 𝒜 (a * d) T where
  morphism := q.morphism
  lineBundle := RingedSpace.TensorPower.sheaf q.lineBundle a
  lineBundle_invertible :=
    Scheme.Modules.Invertible.tensorPower_isInvertible q.lineBundle_invertible a
  psi := powerPsi q a
  psi_map_one := sorry
  psi_map_mul := sorry
  degreeOneMap := powerDegreeOneMap q a
  degreeOneMap_spec := sorry
  degreeOne_surjective := powerDegreeOneMap_epi q a ha

/-- The degree change does not change the structure morphism. -/
theorem power_morphism (q : RelativeProjDegreeQuadruple 𝒜 d T)
    (a : ℕ) (ha : 1 ≤ a) : (power q a ha).morphism = q.morphism := rfl

/-- The new line bundle is the specified tensor power. -/
theorem power_lineBundle (q : RelativeProjDegreeQuadruple 𝒜 d T)
    (a : ℕ) (ha : 1 ≤ a) :
    (power q a ha).lineBundle = RingedSpace.TensorPower.sheaf q.lineBundle a := rfl

/-- Every new homogeneous component is the explicit restricted component. -/
theorem power_psi (q : RelativeProjDegreeQuadruple 𝒜 d T)
    (a : ℕ) (ha : 1 ≤ a) (n : ℕ) :
    (power q a ha).psi n = powerPsi q a n := rfl

/-- A positive divisible target degree has positive quotient. -/
theorem quotient_positive {e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) (h : d ∣ e) :
    1 ≤ e / d := sorry

/-- The canonical degree transition along divisibility, using the determined
quotient `e / d` and transporting only the arithmetic degree equality. -/
def transition (q : RelativeProjDegreeQuadruple 𝒜 d T) {e : ℕ}
    (hd : 1 ≤ d) (he : 1 ≤ e) (h : d ∣ e) :
    RelativeProjDegreeQuadruple 𝒜 e T :=
  (Nat.div_mul_cancel h) ▸ power q (e / d) (quotient_positive hd he h)

/-- Tensor-power degree change preserves strict equivalence of quadruples. -/
theorem power_strictlyEquivalent {q q' : RelativeProjDegreeQuadruple 𝒜 d T}
    (h : StrictlyEquivalent 𝒜 d q q') (a : ℕ) (ha : 1 ≤ a) :
    StrictlyEquivalent 𝒜 (a * d) (power q a ha) (power q' a ha) := sorry

/-- Divisibility degree transitions preserve strict equivalence. -/
theorem transition_strictlyEquivalent {q q' : RelativeProjDegreeQuadruple 𝒜 d T}
    (hqq' : StrictlyEquivalent 𝒜 d q q') {e : ℕ}
    (hd : 1 ≤ d) (he : 1 ≤ e) (h : d ∣ e) :
    StrictlyEquivalent 𝒜 e (transition q hd he h) (transition q' hd he h) := sorry

end AlgebraicGeometry.RelativeProjDegreeQuadruple

namespace AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor.IsAssociatedToQuadruples

variable {S : Scheme.{u}} {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf}
variable {d e : ℕ} {F_d : Scheme.RelativeProjDegreeFunctor S 𝒜 d}
  {F_e : Scheme.RelativeProjDegreeFunctor S 𝒜 e}

/-- Select a representative from the specified degreewise classification. The
transition below is independent of this representative by strict equivalence. -/
def representative (h : F_d.IsAssociatedToQuadruples) (T : Scheme.{u})
    (x : F_d.toFunctor.obj (op T)) : RelativeProjDegreeQuadruple 𝒜 d T :=
  Classical.choose (h.exists_quadruple T x)

/-- The selected representative satisfies the supplied classification relation. -/
theorem representative_spec (h : F_d.IsAssociatedToQuadruples) (T : Scheme.{u})
    (x : F_d.toFunctor.obj (op T)) : h.associated T x (h.representative T x) :=
  Classical.choose_spec (h.exists_quadruple T x)

/-- The point classified by an actual quadruple, with uniqueness supplied by
the classification's equality criterion. -/
def pointOf (h : F_d.IsAssociatedToQuadruples) (T : Scheme.{u})
    (q : RelativeProjDegreeQuadruple 𝒜 d T) : F_d.toFunctor.obj (op T) :=
  Classical.choose (h.exists_point T q)

/-- The classifying point represents exactly the supplied quadruple. -/
theorem pointOf_spec (h : F_d.IsAssociatedToQuadruples) (T : Scheme.{u})
    (q : RelativeProjDegreeQuadruple 𝒜 d T) : h.associated T (h.pointOf T q) q :=
  Classical.choose_spec (h.exists_point T q)

/-- Strictly equivalent representatives determine the same classifying point. -/
theorem pointOf_eq_of_strictlyEquivalent (h : F_d.IsAssociatedToQuadruples)
    (T : Scheme.{u}) (q q' : RelativeProjDegreeQuadruple 𝒜 d T)
    (hqq' : RelativeProjDegreeQuadruple.StrictlyEquivalent 𝒜 d q q') :
    h.pointOf T q = h.pointOf T q' := sorry

/-- Degree transition on classified points: tensor-power the representative,
restrict its Veronese map, then take its class in the target degree. -/
def transitionPoint (hD : F_d.IsAssociatedToQuadruples)
    (hE : F_e.IsAssociatedToQuadruples) (hde : d ∣ e)
    (T : Scheme.{u}) (x : F_d.toFunctor.obj (op T)) : F_e.toFunctor.obj (op T) :=
  hE.pointOf T ((hD.representative T x).transition F_d.degree_pos F_e.degree_pos hde)

/-- Any representative, not just the selected one, computes the degree transition. -/
theorem transitionPoint_eq (hD : F_d.IsAssociatedToQuadruples)
    (hE : F_e.IsAssociatedToQuadruples) (hde : d ∣ e)
    (T : Scheme.{u}) (x : F_d.toFunctor.obj (op T))
    (q : RelativeProjDegreeQuadruple 𝒜 d T) (hq : hD.associated T x q) :
    transitionPoint hD hE hde T x =
      hE.pointOf T (q.transition F_d.degree_pos F_e.degree_pos hde) := sorry

/-- Canonical tensor/restriction degree transition, natural for geometric pullback. -/
def transition (hD : F_d.IsAssociatedToQuadruples)
    (hE : F_e.IsAssociatedToQuadruples) (hde : d ∣ e) :
    F_d.toFunctor ⟶ F_e.toFunctor where
  app T := TypeCat.ofHom (transitionPoint hD hE hde T.unop)
  naturality := sorry

/-- The transition keeps the structure morphism of its quadruple. -/
theorem transition_baseMap (hD : F_d.IsAssociatedToQuadruples)
    (hE : F_e.IsAssociatedToQuadruples) (hde : d ∣ e) :
    transition hD hE hde ≫ F_e.baseMap = F_d.baseMap := sorry

/-- Changing a positive degree to itself fixes the represented point. -/
theorem transition_self (hD : F_d.IsAssociatedToQuadruples) :
    transition hD hD (dvd_refl d) = 𝟙 F_d.toFunctor := sorry

/-- Iterated restriction and tensor powers agree with the direct degree transition. -/
theorem transition_comp {f : ℕ} {F_f : Scheme.RelativeProjDegreeFunctor S 𝒜 f}
    (hD : F_d.IsAssociatedToQuadruples) (hE : F_e.IsAssociatedToQuadruples)
    (hF : F_f.IsAssociatedToQuadruples) (hde : d ∣ e) (hef : e ∣ f) :
    transition hD hE hde ≫ transition hE hF hef =
      transition hD hF (dvd_trans hde hef) := sorry

end AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor.IsAssociatedToQuadruples
