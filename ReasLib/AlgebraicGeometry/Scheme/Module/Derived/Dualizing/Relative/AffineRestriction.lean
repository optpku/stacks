module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AffineOpenSquare
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDualizingComplex

variable {X S : Scheme.{u}} {f : X ⟶ S}
variable [Flat f] [LocallyOfFinitePresentation f]
variable {W : (pullback f f).Opens} {δ : X ⟶ W.toScheme} [IsClosedImmersion δ]
variable {hδ : δ ≫ W.ι = pullback.diagonal f}
variable [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
variable [MonoidalCategory (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)]
variable [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal]
variable {H : MonoidalClosed (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)}

/-- Regard the complex underlying a scheme-relative dualizing complex as a derived module
with quasicoherent cohomology. -/
noncomputable def toDerivedQCoh (C : RelativeDualizingComplex f W δ hδ H) :
    AlgebraicGeometry.Scheme.DerivedQCoh X :=
  ⟨C.complex,
    ModuleDerived.PseudoCoherent.derivedQuasiCoherentModuleProperty
      ((ModuleDerived.isPerfectRelativeTo_iff f C.complex).mp C.isPerfect).1⟩

/-- The derived module underlying `C.toDerivedQCoh` is `C.complex`. -/
theorem toDerivedQCoh_obj (C : RelativeDualizingComplex f W δ hδ H) :
    C.toDerivedQCoh.obj = C.complex := sorry

/-- Restrict a scheme-relative dualizing complex to an affine open and take derived affine
global sections. -/
noncomputable def affineRestriction
    {A : Type u} [CommRing A] (C : RelativeDualizingComplex f W δ hδ H)
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j] :
    DerivedCategory (ModuleCat A) :=
  (AlgebraicGeometry.Scheme.DerivedQCoh.affineGlobalSections (CommRingCat.of A)).obj
    ((AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion.pullback j).obj C.toDerivedQCoh)

/-- `C.affineRestriction j` is affine global sections of the derived open restriction of
`C.toDerivedQCoh`. -/
theorem affineRestriction_def
    {A : Type u} [CommRing A] (C : RelativeDualizingComplex f W δ hδ H)
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j] :
    C.affineRestriction j =
      (AlgebraicGeometry.Scheme.DerivedQCoh.affineGlobalSections (CommRingCat.of A)).obj
        ((AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion.pullback j).obj C.toDerivedQCoh) := sorry

/-- Restriction of a relative dualizing complex to a commutative square of affine open
immersions is relative dualizing for the induced affine algebra map. -/
theorem affineRestriction_isRelativeDualizingComplex
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (W : (pullback f f).Opens) (δ : X ⟶ W.toScheme) [IsClosedImmersion δ]
    (hδ : δ ≫ W.ι = pullback.diagonal f)
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal]
    (H : MonoidalClosed (RingedSpace.ModuleDerived W.toScheme.toRingedSpace))
    (C : Scheme.RelativeDualizingComplex f W δ hδ H)
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]
    (i : Spec (CommRingCat.of R) ⟶ S) [IsOpenImmersion i]
    (hcomm : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ i) :
    @CategoryTheory.DerivedCategory.IsRelativeDualizingComplex R _ A _ _
      (Scheme.Hom.flatOfOpenSquare f j i hcomm)
      (Scheme.Hom.finitePresentationOfOpenSquare f j i hcomm)
      (C.affineRestriction j) := sorry

end AlgebraicGeometry.Scheme.RelativeDualizingComplex
