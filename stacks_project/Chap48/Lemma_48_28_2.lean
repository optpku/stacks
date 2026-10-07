module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Relative.AffineRestriction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 48.28.2: a scheme-relative dualizing complex restricts along a commutative
square of affine open immersions to a relative dualizing complex for the induced ring map. -/
@[stacks 0E2U] #check
  (AlgebraicGeometry.Scheme.RelativeDualizingComplex.affineRestriction_isRelativeDualizingComplex :
    ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
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
      (hcomm : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ i),
      @CategoryTheory.DerivedCategory.IsRelativeDualizingComplex R _ A _ _
        (Scheme.Hom.flatOfOpenSquare f j i hcomm)
        (Scheme.Hom.finitePresentationOfOpenSquare f j i hcomm)
        (C.affineRestriction j))
