/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.ModuleLowerShriek
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Quasicoherent

/-!
# Quasi-coherence of module lower shriek

On an algebraic stack, module lower shriek along the lisse-étale and
flat-fppf inclusions preserves quasi-coherence.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Ring-to-abelian-group sheaf composition exists on every slice of the
lisse-étale topology of an algebraic stack. -/
instance lisseEtaleTopology_over_hasSheafCompose
    (X : GroupoidsOver S) [AlgebraicStack X] :
    ∀ x, ((lisseEtaleTopology X).over x).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Weak sheafification of abelian groups exists on every slice of the
lisse-étale topology of an algebraic stack. -/
instance lisseEtaleTopology_over_hasWeakSheafify
    (X : GroupoidsOver S) [AlgebraicStack X] :
    ∀ x, HasWeakSheafify ((lisseEtaleTopology X).over x) AddCommGrpCat.{u} :=
  sorry

/-- On every slice of the lisse-étale topology of an algebraic stack,
sheafification equivalences are the locally bijective morphisms. -/
instance lisseEtaleTopology_over_wEqualsLocallyBijective
    (X : GroupoidsOver S) [AlgebraicStack X] :
    ∀ x, ((lisseEtaleTopology X).over x).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

/-- Ring-to-abelian-group sheaf composition exists on every slice of the
flat-fppf topology of an algebraic stack. -/
instance flatFppfTopology_over_hasSheafCompose
    (X : GroupoidsOver S) [AlgebraicStack X] :
    ∀ x, ((flatFppfTopology X).over x).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Weak sheafification of abelian groups exists on every slice of the
flat-fppf topology of an algebraic stack. -/
instance flatFppfTopology_over_hasWeakSheafify
    (X : GroupoidsOver S) [AlgebraicStack X] :
    ∀ x, HasWeakSheafify ((flatFppfTopology X).over x) AddCommGrpCat.{u} :=
  sorry

/-- On every slice of the flat-fppf topology of an algebraic stack,
sheafification equivalences are the locally bijective morphisms. -/
instance flatFppfTopology_over_wEqualsLocallyBijective
    (X : GroupoidsOver S) [AlgebraicStack X] :
    ∀ x, ((flatFppfTopology X).over x).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

variable {X : GroupoidsOver S} [AlgebraicStack X]

namespace lisseEtaleModuleLowerShriek

/-- Module lower shriek from the lisse-étale site of an algebraic stack to its
étale site preserves quasi-coherent modules. -/
instance obj_isQuasicoherent
    (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X))
    [H.IsQuasicoherent] :
    ((lisseEtaleModuleLowerShriek X).obj H).IsQuasicoherent :=
  sorry

end lisseEtaleModuleLowerShriek

namespace flatFppfModuleLowerShriek

/-- Module lower shriek from the flat-fppf site of an algebraic stack to its
fppf site preserves quasi-coherent modules. -/
instance obj_isQuasicoherent
    (H : SheafOfModules.{u} (flatFppfStructureSheaf X))
    [H.IsQuasicoherent] :
    ((flatFppfModuleLowerShriek X).obj H).IsQuasicoherent :=
  sorry

end flatFppfModuleLowerShriek

end AlgebraicGeometry.AlgebraicStack
