module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Affine
import StacksCheckRecall

/-!
# Example 29.6.4

The scheme-theoretic image of a map of affine spectra is the spectrum of the quotient by the
kernel of the corresponding ring map.

@stack 056A
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Example 29.6.4: If a ring map has kernel `I`, the scheme-theoretic image of its map on
spectra is the closed subscheme `Spec (A ⧸ I)` of `Spec A`. -/
@[stacks 056A] #check
  (AlgebraicGeometry.schemeTheoreticImage_specMap_iso_quotientOfKernel :
    ∀ {A B : CommRingCat.{u}} (phi : A ⟶ B) (I : Ideal A),
      RingHom.ker phi.hom = I →
        ∃ e : Scheme.Hom.image (Spec.map phi) ≅ Spec (CommRingCat.of (A ⧸ I)),
          e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
            Scheme.Hom.imageι (Spec.map phi))
