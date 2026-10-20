/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage

/-!
# Quasi-coherent higher direct images on algebraic spaces

Along a quasi-compact and quasi-separated morphism of algebraic spaces, higher
direct images of quasi-coherent modules remain quasi-coherent and therefore
restrict to functors `QCoh X ⥤ QCoh Y`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

namespace QCoh

namespace higherDirectImage

/-- Qcqs higher direct images carry quasi-coherent modules to quasi-coherent modules. -/
theorem mapsTo (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (i : ℕ) :
    quasiCoherentModuleProperty X ≤
      (quasiCoherentModuleProperty Y).inverseImage (Modules.higherDirectImageFunctor f i) :=
  sorry

end higherDirectImage

/-- Higher direct image along a qcqs morphism, restricted to quasi-coherent modules. -/
noncomputable def higherDirectImage (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (i : ℕ) : QCoh X ⥤ QCoh Y :=
  FullSubcategory.restrict (Modules.higherDirectImageFunctor f i) (higherDirectImage.mapsTo f i)

/-- Forgetting quasi-coherence after restricted higher direct image recovers ambient
module-sheaf higher direct image. -/
noncomputable def higherDirectImage.inclusionIso (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (i : ℕ) :
    higherDirectImage f i ⋙ inclusion Y ≅
      inclusion X ⋙ Modules.higherDirectImageFunctor f i :=
  FullSubcategory.restrict.compιIso (Modules.higherDirectImageFunctor f i)
    (higherDirectImage.mapsTo f i)

namespace higherDirectImage

/-- The underlying module sheaf of quasi-coherent higher direct image is ambient
module-sheaf higher direct image. -/
@[simp]
theorem obj_obj (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (i : ℕ) (F : QCoh X) :
    ((higherDirectImage f i).obj F).obj = Modules.higherDirectImage f F.obj i :=
  rfl

/-- The underlying morphism of quasi-coherent higher direct image is the ambient
higher direct image of the underlying morphism. -/
@[simp]
theorem map_hom (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (i : ℕ) {F G : QCoh X} (phi : F ⟶ G) :
    ((higherDirectImage f i).map phi).hom = Modules.higherDirectImageMap f phi.hom i :=
  rfl

end higherDirectImage

end QCoh

namespace Modules.higherDirectImage

/-- Higher direct images of quasi-coherent modules along a quasi-compact and
quasi-separated morphism of algebraic spaces remain quasi-coherent. -/
instance isQuasicoherent (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    (higherDirectImage f F i).IsQuasicoherent :=
  QCoh.higherDirectImage.mapsTo f i F inferInstance

/-- A module with an explicit quasi-coherence proof has quasi-coherent higher direct
images along a quasi-compact and quasi-separated morphism. -/
theorem isQuasicoherentOf (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    {F : X.Modules} (hF : F.IsQuasicoherent) (i : ℕ) :
    (higherDirectImage f F i).IsQuasicoherent :=
  QCoh.higherDirectImage.mapsTo f i F hF

end Modules.higherDirectImage

end AlgebraicGeometry.AlgebraicSpace
