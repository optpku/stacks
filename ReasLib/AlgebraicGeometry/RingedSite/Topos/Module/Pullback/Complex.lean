module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of complexes along arbitrary morphisms of ringed topoi

The module inverse image attached to `RingedSite.ToposHom` is additive, hence acts degreewise on
unbounded cochain complexes.  The resulting functor is explicit data and does not depend on a
presentation of the morphism by a functor between sites.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe uX vX uY vY w

namespace RingedSite.ToposHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]

/-- Module pullback along an arbitrary morphism of ringed topoi is additive. -/
theorem modulePullback_additive
    (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] :
    f.modulePullback.Additive := sorry

/-- Pullback of modules along an arbitrary morphism of ringed topoi, applied degreewise to
unbounded cochain complexes. -/
@[stacks 03D6 "complexes, ringed-topos"]
noncomputable def modulePullbackComplex
    (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] :
    CochainComplex (SheafOfModules.{w} Y.structureSheaf) ℤ ⥤
      CochainComplex (SheafOfModules.{w} X.structureSheaf) ℤ :=
  @Functor.mapHomologicalComplex _ _ _ _ _ _ _ f.modulePullback
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ f.modulePullback
      (modulePullback_additive f)) (up ℤ)

/-- Module pullback induces the degreewise pullback functor on cochain homotopy categories. -/
noncomputable def modulePullbackHomotopy
    (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] :
    HomotopyCategory (SheafOfModules.{w} Y.structureSheaf) (up ℤ) ⥤
      HomotopyCategory (SheafOfModules.{w} X.structureSheaf) (up ℤ) :=
  @Functor.mapHomotopyCategory _ _ _ _ _ _ _ f.modulePullback
    (modulePullback_additive f) (up ℤ)

namespace modulePullbackComplex

/-- In every degree, ringed-topos complex pullback is the underlying module pullback. -/
@[simp]
theorem obj_X
    (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]
    (K : CochainComplex (SheafOfModules.{w} Y.structureSheaf) ℤ) (n : ℤ) :
    ((f.modulePullbackComplex).obj K).X n = f.modulePullback.obj (K.X n) := sorry

end modulePullbackComplex

end RingedSite.ToposHom
