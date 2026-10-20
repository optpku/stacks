/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# Separation properties under base change

DM, quasi-DM, separated, and quasi-separated morphisms of algebraic stacks
are stable under base change along bilimit pseudopullback cones and along
both projections of chosen 2-fibre products.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.DM

/-- DM morphisms of algebraic stacks remain DM along the second projection of
any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [DM f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    DM c.snd := sorry

/-- The first projection of a chosen 2-fibre product is DM whenever the second
leg is a DM morphism of algebraic stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [DM g] :
    DM (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) := sorry

/-- The base change of a DM morphism of algebraic stacks along any
morphism of algebraic stacks is DM. -/
@[stacks 050F]
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [DM f] :
    DM (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.DM

namespace AlgebraicGeometry.AlgebraicStack.QuasiDM

/-- Quasi-DM morphisms of algebraic stacks remain quasi-DM along the second
projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [QuasiDM f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    QuasiDM c.snd := sorry

/-- The first projection of a chosen 2-fibre product is quasi-DM whenever the
second leg is a quasi-DM morphism of algebraic stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [QuasiDM g] :
    QuasiDM (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) := sorry

/-- The base change of a quasi-DM morphism of algebraic stacks along any
morphism of algebraic stacks is quasi-DM. -/
@[stacks 050F]
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [QuasiDM f] :
    QuasiDM (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.QuasiDM

namespace AlgebraicGeometry.AlgebraicStack.Separated

/-- Separated morphisms of algebraic stacks remain separated along the second
projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [Separated f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    Separated c.snd := sorry

/-- The first projection of a chosen 2-fibre product is separated whenever the
second leg is a separated morphism of algebraic stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Separated g] :
    Separated (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) := sorry

/-- The base change of a separated morphism of algebraic stacks along any
morphism of algebraic stacks is separated. -/
@[stacks 050F]
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Separated f] :
    Separated (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Separated

namespace AlgebraicGeometry.AlgebraicStack.QuasiSeparated

/-- Quasi-separated morphisms of algebraic stacks remain quasi-separated along
the second projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [QuasiSeparated f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    QuasiSeparated c.snd := sorry

/-- The first projection of a chosen 2-fibre product is quasi-separated whenever
the second leg is a quasi-separated morphism of algebraic stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [QuasiSeparated g] :
    QuasiSeparated (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) := sorry

/-- The base change of a quasi-separated morphism of algebraic stacks along any
morphism of algebraic stacks is quasi-separated. -/
@[stacks 050F]
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [QuasiSeparated f] :
    QuasiSeparated (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.QuasiSeparated
