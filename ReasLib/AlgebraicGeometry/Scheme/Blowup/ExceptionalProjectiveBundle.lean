module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Syntomic
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Exceptional divisors as projective bundles

This file gives the canonical map from the exceptional divisor of a blowup to the center,
the induced quotient of the pulled-back conormal sheaf, and its comparison with a chosen
projective-bundle representation.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

variable {X X' : Scheme.{u}}

/-- The exceptional divisor of a blowup maps canonically to its center. -/
def exceptionalProjection (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I] :
    (I.comap b).subscheme ⟶ I.subscheme :=
  Scheme.IdealSheafData.subschemeMap (I.comap b) I b (I.le_map_comap b)

/-- The exceptional projection followed by the center immersion is the exceptional immersion
followed by the blowup morphism. -/
theorem exceptionalProjection_subschemeι (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] :
    exceptionalProjection I b ≫ I.subschemeι = (I.comap b).subschemeι ≫ b := sorry

/-- The canonical conormal map from the pullback of the center's conormal sheaf to the
conormal sheaf of the exceptional divisor. -/
def exceptionalConormalMap (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I] :
    (Scheme.Modules.pullback (exceptionalProjection I b)).obj
        (Scheme.Hom.conormalSheaf I.subschemeι) ⟶
      Scheme.Hom.conormalSheaf (I.comap b).subschemeι :=
  Scheme.Hom.Conormal.map
    (f := exceptionalProjection I b) (i := (I.comap b).subschemeι)
      (i' := I.subschemeι) (g := b) ⟨exceptionalProjection_subschemeι I b⟩

/-- The exceptional conormal map is the conormal comparison for the canonical square formed by
the exceptional and center immersions. -/
theorem exceptionalConormalMap_def (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] :
    exceptionalConormalMap I b =
      Scheme.Hom.Conormal.map
        (f := exceptionalProjection I b) (i := (I.comap b).subschemeι)
          (i' := I.subschemeι) (g := b) ⟨exceptionalProjection_subschemeι I b⟩ := sorry

/-- The exceptional conormal map is an epimorphism. -/
theorem exceptionalConormalMap_epi (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] : Epi (exceptionalConormalMap I b) := sorry

/-- The conormal sheaf of the exceptional effective Cartier divisor is invertible. -/
theorem exceptionalConormal_isInvertible (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] :
    Scheme.Modules.Invertible (Scheme.Hom.conormalSheaf (I.comap b).subschemeι) := sorry

/-- The exceptional conormal map, bundled as an invertible quotient. -/
def exceptionalConormalQuotient (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I] :
    CategoryTheory.InvertibleQuotient
      ((Scheme.Modules.pullback (exceptionalProjection I b)).obj
        (Scheme.Hom.conormalSheaf I.subschemeι)) where
  object := Scheme.Hom.conormalSheaf (I.comap b).subschemeι
  isInvertible := exceptionalConormal_isInvertible I b
  hom := exceptionalConormalMap I b
  hom_epi := exceptionalConormalMap_epi I b

/-- The target of the exceptional conormal quotient is the conormal sheaf of the exceptional
divisor. -/
theorem exceptionalConormalQuotient_object (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] :
    (exceptionalConormalQuotient I b).object =
      Scheme.Hom.conormalSheaf (I.comap b).subschemeι := sorry

/-- The morphism of the exceptional conormal quotient is the canonical conormal map. -/
theorem exceptionalConormalQuotient_hom (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] :
    (exceptionalConormalQuotient I b).hom = exceptionalConormalMap I b := sorry

variable {P : Scheme.{u}}

/-- The lift of the exceptional projection to a chosen projective-bundle representation of the
center's conormal sheaf. -/
def exceptionalProjectiveLift (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] (q : P ⟶ I.subscheme)
    (hP : Scheme.ProjectiveBundle.Representation q
      (Scheme.Hom.conormalSheaf I.subschemeι)) :
    Scheme.ProjectiveBundle.Lift q (exceptionalProjection I b) :=
  (hP.liftEquiv (exceptionalProjection I b)).symm (exceptionalConormalQuotient I b)

/-- The exceptional projective lift lies over the canonical exceptional projection. -/
theorem exceptionalProjectiveLift_fac (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] (q : P ⟶ I.subscheme)
    (hP : Scheme.ProjectiveBundle.Representation q
      (Scheme.Hom.conormalSheaf I.subschemeι)) :
    (exceptionalProjectiveLift I b q hP).hom ≫ q = exceptionalProjection I b := sorry

/-- The canonical comparison from the exceptional divisor to a chosen projective-bundle model
of the center's conormal sheaf. -/
def exceptionalProjectiveComparison (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] (q : P ⟶ I.subscheme)
    (hP : Scheme.ProjectiveBundle.Representation q
      (Scheme.Hom.conormalSheaf I.subschemeι)) :
    (I.comap b).subscheme ⟶ P :=
  (exceptionalProjectiveLift I b q hP).hom

/-- The exceptional projective comparison is a morphism over the center. -/
theorem exceptionalProjectiveComparison_over (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] (q : P ⟶ I.subscheme)
    (hP : Scheme.ProjectiveBundle.Representation q
      (Scheme.Hom.conormalSheaf I.subschemeι)) :
    exceptionalProjectiveComparison I b q hP ≫ q = exceptionalProjection I b := sorry

/-- For a regular center, the canonical comparison from the exceptional divisor to its
projective-bundle model is an isomorphism. -/
theorem exceptionalProjectiveComparison_isIso (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] [IsRegularImmersion I.subschemeι] (q : P ⟶ I.subscheme)
    (hP : Scheme.ProjectiveBundle.Representation q
      (Scheme.Hom.conormalSheaf I.subschemeι)) :
    IsIso (exceptionalProjectiveComparison I b q hP) := sorry

/-- If the ambient scheme and center are smooth over a common base, the exceptional divisor is
canonically isomorphic to every chosen projective-bundle model of the center's conormal sheaf. -/
theorem exceptionalProjectiveComparison_isIso_of_smooth {S : Scheme.{u}}
    (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X) [Smooth f]
    [Smooth (I.subschemeι ≫ f)] [IsBlowup b I] (q : P ⟶ I.subscheme)
    (hP : Scheme.ProjectiveBundle.Representation q
      (Scheme.Hom.conormalSheaf I.subschemeι)) :
    IsIso (exceptionalProjectiveComparison I b q hP) := sorry

/-- The pullback-to-conormal comparison for the exceptional divisor is an isomorphism. -/
theorem exceptionalPullbackIdealComparison_isIso (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] :
    IsIso (Scheme.Hom.Conormal.pullbackIdealComparison (I.comap b).subschemeι) := sorry

/-- The conormal sheaf of the exceptional divisor is canonically the restriction of its
negative-divisor sheaf. -/
def exceptionalConormalNegIso (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I] :
    Scheme.Hom.conormalSheaf (I.comap b).subschemeι ≅
      (Scheme.Modules.pullback (I.comap b).subschemeι).obj (I.comap b).negSheaf :=
  -- Local instance justification (proof-local temporary data): `asIso` needs the proved `IsIso` only while constructing this explicit isomorphism.
  letI := exceptionalPullbackIdealComparison_isIso I b
  (asIso
    ((Scheme.Modules.pullback (I.comap b).subschemeι).map (I.comap b).toModuleIso.hom ≫
      Scheme.Hom.Conormal.pullbackIdealComparison (I.comap b).subschemeι)).symm

/-- The exceptional conormal-to-negative-sheaf isomorphism is inverse to the canonical
pullback-ideal comparison. -/
theorem exceptionalConormalNegIso_hom_comp (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] :
    (exceptionalConormalNegIso I b).hom ≫
        (Scheme.Modules.pullback (I.comap b).subschemeι).map (I.comap b).toModuleIso.hom ≫
        Scheme.Hom.Conormal.pullbackIdealComparison (I.comap b).subschemeι =
      𝟙 (Scheme.Hom.conormalSheaf (I.comap b).subschemeι) := sorry

/-- The tautological sheaf pulled back along the exceptional projective comparison is
canonically the restriction of the negative exceptional-divisor sheaf. -/
def exceptionalTautologicalIso (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] (q : P ⟶ I.subscheme)
    (hP : Scheme.ProjectiveBundle.Representation q
      (Scheme.Hom.conormalSheaf I.subschemeι)) :
    (Scheme.Modules.pullback (exceptionalProjectiveComparison I b q hP)).obj
        (Scheme.ProjectiveBundle.tautologicalSheaf q hP) ≅
      (Scheme.Modules.pullback (I.comap b).subschemeι).obj (I.comap b).negSheaf :=
  hP.pullbackTautologicalSheafIso (exceptionalProjection I b)
      (exceptionalProjectiveLift I b q hP) ≪≫
    eqToIso (congrArg CategoryTheory.InvertibleQuotient.object
      (Equiv.apply_symm_apply (hP.liftEquiv (exceptionalProjection I b))
        (exceptionalConormalQuotient I b))) ≪≫
    exceptionalConormalNegIso I b

/-- For a blowup in a center smooth over the same base as the ambient scheme, the pulled-back
tautological sheaf is canonically the restriction of the negative exceptional-divisor sheaf. -/
def exceptionalTautologicalIso_of_smooth {S : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) (b : X' ⟶ X) [Smooth f] [Smooth (I.subschemeι ≫ f)]
    [IsBlowup b I] (q : P ⟶ I.subscheme)
    (hP : Scheme.ProjectiveBundle.Representation q
      (Scheme.Hom.conormalSheaf I.subschemeι)) :
    (Scheme.Modules.pullback (exceptionalProjectiveComparison I b q hP)).obj
        (Scheme.ProjectiveBundle.tautologicalSheaf q hP) ≅
      (Scheme.Modules.pullback (I.comap b).subschemeι).obj (I.comap b).negSheaf :=
  exceptionalTautologicalIso I b q hP

/-- The exceptional tautological isomorphism carries the pulled-back tautological quotient map
to the exceptional conormal quotient, followed by the negative-sheaf comparison. -/
theorem exceptionalTautologicalIso_hom (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] (q : P ⟶ I.subscheme)
    (hP : Scheme.ProjectiveBundle.Representation q
      (Scheme.Hom.conormalSheaf I.subschemeι)) :
    (Scheme.Modules.pullback (exceptionalProjectiveComparison I b q hP)).map
          (Scheme.ProjectiveBundle.tautologicalQuotient q hP).hom ≫
        (exceptionalTautologicalIso I b q hP).hom =
      (Scheme.ProjectiveBundle.Lift.pullbackSourceIso
          (exceptionalProjectiveLift I b q hP)
          (Scheme.Hom.conormalSheaf I.subschemeι)).hom ≫
        (exceptionalConormalQuotient I b).hom ≫ (exceptionalConormalNegIso I b).hom := sorry

end AlgebraicGeometry.IsBlowup
