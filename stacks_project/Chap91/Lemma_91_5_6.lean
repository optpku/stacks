module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatLift.Torsor
import StacksCheckRecall

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open AlgebraicGeometry.RingedSpace.Thickening.Hom (FlatLift)
open scoped AlgebraicGeometry

universe u w

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift

/-- The legacy chart on associated infinitesimal extensions identifies extension
classes with identity-comparison infinitesimal extension classes by Baer translation
from the extension of a chosen flat lift. -/
abbrev isoClassEquiv {T U : Thickening.{u}} [IsFirstOrderThickening T.hom]
    [IsFirstOrderThickening U.hom] {g : T ⟶ U} {F : T.left.Modules}
    (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left] (L0 : FlatLift g F) :
    ExtensionClass (idealModule T.hom ⊗ F) F ≃
      InfinitesimalExtension.IsoClass T.hom F (idealModule T.hom ⊗ F)
        (infMapId T.hom F) :=
  InfinitesimalExtension.isoClassEquiv (toInfinitesimalExtension hg L0)

end AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift

/- Lemma 91.5.6. For a strict morphism of first-order thickenings and a module flat
over the reduced base, existence of a flat lift makes the isomorphism classes of
flat lift pairs principal homogeneous under Ext¹(F, ℐ ⊗ F), as expressed by the
canonical bijective differences and their additive cocycle identity. -/
@[stacks 08LM] #check
  (AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift.principalHomogeneous :
    ∀ {T U : Thickening.{u}} [IsFirstOrderThickening T.hom]
      [IsFirstOrderThickening U.hom] {g : T ⟶ U} {F : T.left.Modules}
      (hg : Thickening.Hom.IsStrict g) [SheafOfModules.IsFlatOver F g.left]
      [HasExt.{w} T.left.Modules] (L0 : FlatLift g F),
      Nonempty (FlatLift.IsomorphismClass g F) ∧
        (∀ p : FlatLift.IsomorphismClass g F,
          Function.Bijective (fun q : FlatLift.IsomorphismClass g F => FlatLift.difference hg q p)) ∧
        (∀ p q r : FlatLift.IsomorphismClass g F,
          FlatLift.difference hg p r = FlatLift.difference hg p q + FlatLift.difference hg q r))
