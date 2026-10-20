module

public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.Ext
public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.Obstruction
public import ReasLib.CategoryTheory.Abelian.Extension.Basic
import StacksCheckRecall

/-!
# Trivial infinitesimal extensions and their canonical Ext classes

A retraction defines the split extension with any prescribed ideal action. Restricting
along that retraction classifies the extensions by Ext¹, with the split extension at zero.
The scalar-comparison equivalence identifies mixed-scalar maps with all intrinsic maps
`idealModule i ⊗ F ⟶ K`.
-/

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian (Ext)
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
open AlgebraicGeometry.RingedSpace.Modules
open AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension

/-- Restriction along a trivialization, presented as an extension with fixed endpoints. -/
public noncomputable def restrictExtension
    {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
    (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    (E : InfinitesimalExtension i F K c) : Extension K F where
  E := (restrictionShortComplex τ E).X₂
  f := (restrictionShortComplex τ E).f
  g := (restrictionShortComplex τ E).g
  zero := (restrictionShortComplex τ E).zero
  shortExact := restrictionShortComplex_shortExact τ E

end AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension

#check (AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.trivialExtension :
  ∀ {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i],
    (τ : Trivialization i) → {F K : X.Modules} →
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) →
    InfinitesimalExtension i F K c)

#check (AlgebraicGeometry.RingedSpace.Modules.infinitesimalComparisonEquiv :
  ∀ {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i]
    (F K : X.Modules),
    (kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) ≃
      (idealModule i ⊗ F ⟶ K))

#check (AlgebraicGeometry.RingedSpace.Modules.infinitesimalComparisonEquiv_apply :
  ∀ {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i]
    (F K : X.Modules) (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K),
    infinitesimalComparisonEquiv i F K c = infinitesimalMap_restrict i c)

#check (AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.extClass :
  ∀ {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
    [HasExt.{u} X.Modules] (_τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K},
    InfinitesimalExtension i F K c → Ext F K 1)

/- Remark 91.4.6. Restriction along a chosen trivialization classifies extensions with
prescribed infinitesimal map; the explicit trivial extension represents the zero class. -/
@[stacks 08LB] #check
  (AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.extClass_bijective :
    ∀ {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
      [HasExt.{u} X.Modules] (τ : Trivialization i) {F K : X.Modules}
      (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K),
      Function.Bijective (extClassOnIsoClass τ c))

#check (AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.extClass_trivial :
  ∀ {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
    [HasExt.{u} X.Modules] (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K),
    extClass τ (trivialExtension τ c) = 0)
