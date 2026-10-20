/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Module.DualizingSheaf
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)

/- Canonical companion (1): a scheme. -/
#check (AlgebraicGeometry.Scheme : Type (u + 1))

#check (Scheme.forgetToLocallyRingedSpace : Scheme.{u} ⥤ LocallyRingedSpace.{u})

/- Canonical companion (2): a morphism of schemes is a morphism of the
underlying locally ringed spaces. -/
#check (Scheme.Hom : Scheme.{u} → Scheme.{u} → Type u)

#check (Scheme.Hom.toLRSHom : ∀ {X Y : Scheme.{u}},
  X.Hom Y → (X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace))
#check (inferInstance : Category Scheme.{u})

/- Canonical companion (3): a quasi-coherent module on a scheme. -/
#check (F.IsQuasicoherent : Prop)

section
variable {k : Type u} [Field k] (V : SchemeOverField k)

/- Canonical companion (4): a variety over a field `k`. -/
#check (Variety V : Prop)

#check (SchemeOverField k : Type (u + 1))

#check (variety_iff V :
  Variety V ↔ IsIntegral V.left ∧ IsSeparated V.hom ∧ Scheme.Hom.FiniteType V.hom)

/- Canonical companion (5): a curve over a field `k`. -/
#check (Curve V : Prop)

#check (curve_iff V : Curve V ↔ Variety V ∧ topologicalKrullDim V.left = 1)

end

/- Canonical companion (6): a finite morphism of schemes. -/
#check (IsFinite f : Prop)

#check (isFinite_iff f :
  IsFinite f ↔
    IsAffineHom f ∧
      ∀ U : Y.Opens, IsAffineOpen U → (f.app U).hom.Finite)

section
open TopologicalSpace

variable {X : TopCat.{u}} (F : X.Sheaf AddCommGrpCat.{u})
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]

/- Canonical companion (7): the cohomology of a sheaf of abelian groups `F`
over a topological space `X`. -/
#check (CategoryTheory.Sheaf.H : X.Sheaf AddCommGrpCat.{u} →
  ∀ [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})], ℕ → Type u)

#check (CategoryTheory.Sheaf.H' :
  ∀ [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})],
    X.Sheaf AddCommGrpCat.{u} → ℕ → Opens X → AddCommGrpCat.{u})

end

/- Exercise 111.63.1 (Definitions) (8): a dualizing sheaf on a scheme `X` of dimension `d`
proper over a field `k`, defined by the trace universal property for coherent modules. -/
@[stacks 0G13] #check (AlgebraicGeometry.Scheme.IsDualizingSheaf :
  ∀ {k : Type u} [Field k] {X : Scheme.{u}},
    (X ⟶ Spec (CommRingCat.of k)) → ℕ → X.Modules → Prop)

section

variable {k : Type u} [Field k] (V W : SchemeOverField k) [Variety V] [Variety W]

/- Canonical companion (9): a rational map over `k` from a variety `V`
to a variety `W`, represented by a morphism over `k` on a dense open subscheme. -/
#check ({ρ : V.left ⤏ W.left //
  Scheme.RationalMap.IsOver (Spec (CommRingCat.of k)) ρ} : Type u)

#check (AlgebraicGeometry.Scheme.PartialMap.toRationalMap :
  V.left.PartialMap W.left → (V.left ⤏ W.left))
#check (AlgebraicGeometry.Scheme.RationalMap.exists_rep :
  ∀ ρ : V.left ⤏ W.left, ∃ representative : V.left.PartialMap W.left,
    representative.toRationalMap = ρ)
#check (AlgebraicGeometry.Scheme.PartialMap.toRationalMap_eq_iff :
  ∀ {representative₁ representative₂ : V.left.PartialMap W.left},
    representative₁.toRationalMap = representative₂.toRationalMap ↔
      representative₁.equiv representative₂)

end
