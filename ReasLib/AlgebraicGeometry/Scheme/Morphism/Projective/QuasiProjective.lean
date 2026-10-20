/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-projective scheme morphisms

This file owns quasi-projective, H-quasi-projective, and locally
quasi-projective morphism properties. H-quasi-projective morphisms are
presented by quasi-compact immersions into relative projective spaces, while
the relative-ample criterion lives with scheme modules.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- A scheme morphism is quasi-projective when it is finite type and admits a relatively ample
module on its source. -/
@[stacks 01VW "quasi-projective morphism"]
class QuasiProjective (f : X ⟶ S) : Prop where
  /-- The morphism is of finite type. -/
  toFiniteType : Scheme.Hom.FiniteType f
  /-- A relatively ample module exists. -/
  exists_relativelyAmple :
    ∃ L : X.Modules, RelativelyAmple f L

/-- Characterize quasi-projectivity by finite type and the existence of a relatively ample
module. -/
@[stacks 01VW "quasi-projective characterization"]
theorem quasiProjective_iff :
    QuasiProjective f ↔
      Scheme.Hom.FiniteType f ∧
        ∃ L : X.Modules, RelativelyAmple f L := sorry

/-- A quasi-projective morphism is separated. -/
theorem QuasiProjective.isSeparated [QuasiProjective f] :
    IsSeparated f := sorry

/-- A quasi-projective morphism is of finite type. -/
theorem QuasiProjective.finiteType [QuasiProjective f] :
    Scheme.Hom.FiniteType f := sorry

/-- An H-quasi-projective morphism admits a quasi-compact immersion into a finite-dimensional
relative projective space over its base. -/
@[stacks 01VW "H-quasi-projective morphism"]
class HQuasiProjective (f : X ⟶ S) : Prop where
  /-- A relative projective space and a quasi-compact immersion over the base exist. -/
  exists_presentation :
    ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
      QuasiCompact i ∧ IsImmersion i ∧ i ≫ P.hom = f

/-- Extract the presentation carried by an H-quasi-projective morphism. -/
theorem HQuasiProjective.presentation
    (h : HQuasiProjective f) :
    ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
      QuasiCompact i ∧ IsImmersion i ∧ i ≫ P.hom = f := sorry

/-- An H-quasi-projective morphism is locally of finite type. -/
theorem HQuasiProjective.locallyOfFiniteType
    (h : HQuasiProjective f) :
    LocallyOfFiniteType f := sorry

/-- Characterize H-quasi-projectivity by an immersion into a relative projective space. -/
theorem hQuasiProjective_iff :
    HQuasiProjective f ↔
      ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
        QuasiCompact i ∧ IsImmersion i ∧ i ≫ P.hom = f := sorry

/-- H-quasi-projectivity implies quasi-projectivity. -/
theorem HQuasiProjective.toQuasiProjective
    (h : HQuasiProjective f) :
    QuasiProjective f := sorry

/-- An H-quasi-projective morphism is separated. -/
theorem HQuasiProjective.isSeparated [HQuasiProjective f] :
    IsSeparated f := sorry

/-- An H-quasi-projective morphism is of finite type. -/
theorem HQuasiProjective.finiteType [HQuasiProjective f] :
    Scheme.Hom.FiniteType f := sorry

/-- A morphism is locally quasi-projective when it is quasi-projective after restricting to a
cover of the base. -/
@[stacks 01VW "locally quasi-projective morphism"]
class LocallyQuasiProjective (f : X ⟶ S) : Prop where
  /-- A target open cover on whose members the restricted morphisms are quasi-projective. -/
  exists_cover :
    ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ i : 𝒰.I₀,
      QuasiProjective (f ∣_ ((𝒰.f i).opensRange))

/-- Extract the target open cover carried by a locally quasi-projective morphism. -/
theorem LocallyQuasiProjective.openCover
    (h : LocallyQuasiProjective f) :
    ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ i : 𝒰.I₀,
      QuasiProjective (f ∣_ ((𝒰.f i).opensRange)) := sorry

/-- A quasi-projective morphism is locally quasi-projective. -/
theorem QuasiProjective.toLocallyQuasiProjective
    (h : QuasiProjective f) :
    LocallyQuasiProjective f := sorry

/-- Characterize local quasi-projectivity by a target open cover. -/
theorem locallyQuasiProjective_iff :
    LocallyQuasiProjective f ↔
      ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ i : 𝒰.I₀,
        QuasiProjective (f ∣_ ((𝒰.f i).opensRange)) := sorry

/-- A locally quasi-projective morphism is separated. -/
theorem LocallyQuasiProjective.isSeparated [LocallyQuasiProjective f] :
    IsSeparated f := sorry

/-- A locally quasi-projective morphism is locally of finite type. -/
theorem LocallyQuasiProjective.locallyOfFiniteType [LocallyQuasiProjective f] :
    LocallyOfFiniteType f := sorry

/-- A locally quasi-projective morphism is of finite type. -/
theorem LocallyQuasiProjective.finiteType [LocallyQuasiProjective f] :
    Scheme.Hom.FiniteType f := sorry

end

end AlgebraicGeometry
