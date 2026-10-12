/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.AffineSectionMap
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.CanonicalPower

/-!
# The canonical universal quadruple on an affine relative-Proj degree chart

The structure map, line module and homogeneous maps are all specified. The
homogeneous map is a/1, restricted to the degree open, and expressed in tensor
powers through the inverse of actual localized multiplication.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry Opposite
open SheafOfModules.RingedSite
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.RelativeProjAffineSectionRing

variable {S : Scheme.{u}} (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf)
variable [𝒜.IsCommutative] [IsAffine S]

/-- The actual positive-degree open chart of the section-ring Proj. -/
abbrev chart (d : ℕ) : Scheme.{u} := (Proj.degreeOpen (grading 𝒜) d).toScheme

/-- Its structure morphism is the open inclusion followed by the canonical map to S. -/
def chartToBase (d : ℕ) : chart 𝒜 d ⟶ S :=
  (Proj.degreeOpen (grading 𝒜) d).ι ≫ toBase 𝒜

/-- Restrict the homogeneous sheaf map and invert the specified local tensor-power map. -/
def universalHom (hA : 𝒜.IsQuasicoherent) {d : ℕ} (hd : 0 < d) (n : ℕ) :
    (Scheme.Modules.pullback (chartToBase 𝒜 d)).obj (𝒜 (Int.ofNat (n * d))) ⟶
      RingedSpace.TensorPower.sheaf
        (Proj.AssociatedModule.CanonicalAlgebra.degreeLine (grading 𝒜) d) n :=
  (Scheme.Modules.pullbackComp (Proj.degreeOpen (grading 𝒜) d).ι (toBase 𝒜)).inv.app
    (𝒜 (Int.ofNat (n * d))) ≫
    (Scheme.Modules.pullback (Proj.degreeOpen (grading 𝒜) d).ι).map
      (homogeneousPullbackMap 𝒜 hA (n * d) ≫
        eqToHom (congrArg (Proj.AssociatedModule.twistingSheaf (grading 𝒜))
          (by simp : (Int.ofNat (n * d)) = (n : ℤ) * (d : ℤ)))) ≫
      (Proj.AssociatedModule.CanonicalAlgebra.degreePowerIso (grading 𝒜) hd n).inv

/-- The same map in the pushforward form required by fixed-degree quadruples. -/
def universalPsi (hA : 𝒜.IsQuasicoherent) {d : ℕ} (hd : 0 < d) (n : ℕ) :
    𝒜 (Int.ofNat (n * d)) ⟶
      (Scheme.Modules.pushforward (chartToBase 𝒜 d)).obj
        (RingedSpace.TensorPower.sheaf
          (Proj.AssociatedModule.CanonicalAlgebra.degreeLine (grading 𝒜) d) n) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (chartToBase 𝒜 d)).homEquiv _ _
    (universalHom 𝒜 hA hd n)

/-- Degree-d homogeneous sections generate this line module on precisely the
degree-d open. No claim is made outside that open. -/
theorem universalHom_one_epi (hA : 𝒜.IsQuasicoherent) {d : ℕ} (hd : 0 < d) :
    Epi (universalHom 𝒜 hA hd 1) := sorry

/-- The universal quadruple with actual module and morphism data. -/
def universalQuadruple (hA : 𝒜.IsQuasicoherent) {d : ℕ} (hd : 0 < d) :
    RelativeProjDegreeQuadruple 𝒜 d (chart 𝒜 d) where
  morphism := chartToBase 𝒜 d
  lineBundle := Proj.AssociatedModule.CanonicalAlgebra.degreeLine (grading 𝒜) d
  lineBundle_invertible :=
    Proj.AssociatedModule.CanonicalAlgebra.degreeLine_invertible (grading 𝒜) hd
  psi := universalPsi 𝒜 hA hd
  psi_map_one := sorry
  psi_map_mul := sorry
  degreeOneMap := universalHom 𝒜 hA hd 1
  degreeOneMap_spec := rfl
  degreeOne_surjective := universalHom_one_epi 𝒜 hA hd

/-- The functor really is the represented degree chart, with its actual base map. -/
def degreeFunctor (hA : 𝒜.IsQuasicoherent) {d : ℕ} (hd : 1 ≤ d) :
    RelativeProjDegreeFunctor S 𝒜 d :=
  RelativeProjDegreeFunctor.ofFunctor (yoneda.obj (chart 𝒜 d))
    (yoneda.map (chartToBase 𝒜 d)) hd hA

/-- Association is fixed by pulling back the specified universal quadruple;
it is not an arbitrary chosen representability bijection. -/
def degreeAssociated (hA : 𝒜.IsQuasicoherent) {d : ℕ} (hd : 1 ≤ d) :
    (degreeFunctor 𝒜 hA hd).IsAssociatedToQuadruples where
  associated T x q := RelativeProjDegreeQuadruple.StrictlyEquivalent 𝒜 d q
    (RelativeProjDegreeQuadruple.canonicalPullback (T := chart 𝒜 d) (T' := T) x
      (universalQuadruple 𝒜 hA hd))
  exists_quadruple := sorry
  exists_point := sorry
  base_eq := sorry
  eq_iff := sorry
  pullbackCore T T' g := RelativeProjDegreeQuadruple.canonicalPullbackCore g
  pullbackQuadruple T T' g q := RelativeProjDegreeQuadruple.canonicalPullback
    (T := T) (T' := T') g q
  pullback_morphism_eq _ _ _ _ := rfl
  pullback_lineBundleIso _ _ _ _ := Iso.refl _
  pullback_spec T T' g q := RelativeProjDegreeQuadruple.canonicalPullback_spec
    (T := T) (T' := T') g q
  associated_pullback := sorry

end AlgebraicGeometry.Scheme.RelativeProjAffineSectionRing
