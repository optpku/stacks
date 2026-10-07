module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Restrict
import StacksCheckRecall

/-!
# Lemma 29.6.3

Quasi-compact scheme-theoretic images: their kernel ideal sheaf, restriction to opens,
and dominance of the canonical map.

@stack 01R8
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 29.6.3 (1): for a quasi-compact morphism, the ideal sheaf defining its
scheme-theoretic image is the componentwise kernel of the structure-sheaf map. -/
@[stacks 01R8] #check
  (AlgebraicGeometry.Scheme.Hom.ker_apply :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.QuasiCompact f] (U : Y.affineOpens),
      f.ker.ideal U = RingHom.ker (f.app U).hom)

/- Lemma 29.6.3 (2): the scheme-theoretic image is the closed subscheme cut out by
the kernel ideal sheaf, and the original morphism factors through it. -/
@[stacks 01R8] #check
  (AlgebraicGeometry.Scheme.Hom.image :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}},
      (X ⟶ Y) → AlgebraicGeometry.Scheme.{u})
#check
  (AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData),
      I.subschemeι.ker = I)
#check
  (AlgebraicGeometry.Scheme.Hom.toImage_imageι :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
      f.toImage ≫ f.imageι = f)

/- Lemma 29.6.3 (3): restriction to every target open commutes with the
scheme-theoretic image, canonically and compatibly with the inclusions into that open. -/
@[stacks 01R8] #check
  (AlgebraicGeometry.Scheme.Hom.imageMorphismRestrictIso :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.QuasiCompact f] (U : Y.Opens),
      (f ∣_ U).image ≅ (f.imageι ⁻¹ᵁ U))
#check
  (AlgebraicGeometry.Scheme.Hom.imageMorphismRestrictIso_hom_imageι :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.QuasiCompact f] (U : Y.Opens),
      (f.imageMorphismRestrictIso U).hom ≫ (f.imageι ∣_ U) = (f ∣_ U).imageι)

/- Lemma 29.6.3 (4): the canonical morphism from the source to its
scheme-theoretic image is dominant. -/
@[stacks 01R8] #check
  (AlgebraicGeometry.Scheme.instIsDominantToImageOfQuasiCompact :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.QuasiCompact f],
      AlgebraicGeometry.IsDominant f.toImage)
