module

public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.Torsor
import StacksCheckRecall

/-!
# Isomorphism classes of infinitesimal extensions

A first-order thickening with a chosen extension of prescribed infinitesimal map has
isomorphism classes principal homogeneous under `𝒪_X`-extension classes, canonically
identified with `Ext¹` by `ExtensionClass.toExt`.
-/

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open scoped AlgebraicGeometry

universe u

variable {X X' : RingedSpace.{u}}
variable {i : X ⟶ X'} [IsFirstOrderThickening i]
variable {F K : X.Modules}
variable {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}

/- Lemma 91.4.3. Given a first-order thickening, modules `F`, `K`, and a prescribed
infinitesimal map `c`, a chosen extension with map `c` identifies its isomorphism-class
space with `ExtensionClass K F`, the canonical presentation of `Ext¹(F, K)`. -/
@[stacks 08L7] #check
  (AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.isoClassEquiv :
    (E0 : InfinitesimalExtension i F K c) →
      ExtensionClass K F ≃ InfinitesimalExtension.IsoClass i F K c)
