/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedPoints.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AssociatedPoints
import StacksCheckRecall

/-!
# Definition 71.2.2

Weakly associated points of quasi-coherent modules on algebraic spaces, the
locus `WeakAss(F)`, the space-level locus `WeakAss(X) = WeakAss(𝒪_X)`, and the
locally Noetherian identification `Ass = WeakAss`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Definition 71.2.2 (1): a point `x ∈ |X|` is weakly associated to a
quasi-coherent `𝒪_X`-module `F` when the equivalent étale-chart and étale-stalk
conditions of Lemma 71.2.1 hold. -/
@[stacks 0CTX] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.etaleStalkWeakAss :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → X.Modules → Points X → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.existsEtaleWeakAss_iff_etaleStalkWeakAss :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → (F : X.Modules) → [F.IsQuasicoherent] →
    (x : Points X) → (Modules.existsEtaleWeakAss F x ↔ Modules.etaleStalkWeakAss F x))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.forallEtaleWeakAss_iff_etaleStalk :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → (F : X.Modules) → [F.IsQuasicoherent] →
    (x : Points X) → (Modules.forallEtaleWeakAss F x ↔ Modules.etaleStalkWeakAss F x))

/- Definition 71.2.2 (2): `WeakAss(F)` is the set of weakly associated points of
`F`. -/
@[stacks 0CTX] #check (AlgebraicGeometry.AlgebraicSpace.Modules.weakAss :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → X.Modules → Set (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_weakAss_iff :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → (F : X.Modules) → (x : Points X) →
    (x ∈ F.weakAss ↔ Modules.etaleStalkWeakAss F x))

/- Definition 71.2.2 (3): the weakly associated points of `X` are the weakly
associated points of `𝒪_X`. -/
@[stacks 0CTX] #check (AlgebraicGeometry.AlgebraicSpace.weakAss_eq_weakAss_unit :
  {S : Scheme.{u}} → (X : AlgebraicSpace S) →
    X.weakAss = Modules.weakAss (SheafOfModules.unit (structureSheaf X) : X.Modules))

#check (AlgebraicGeometry.AlgebraicSpace.mem_weakAss_iff_etaleStalkWeakAss :
  {S : Scheme.{u}} → (X : AlgebraicSpace S) → (x : Points X) →
    (x ∈ X.weakAss ↔
      Modules.etaleStalkWeakAss (SheafOfModules.unit (structureSheaf X) : X.Modules) x))

/- Definition 71.2.2 (4): if `X` is locally Noetherian, then `x` is associated to
`F` if and only if it is weakly associated, and `Ass(F) = WeakAss(F)`. -/
@[stacks 0CTX] #check (AlgebraicGeometry.AlgebraicSpace.Modules.associatedPoints :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → [IsLocallyNoetherian X] →
    X.Modules → Set (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.associatedPoints_eq_weakAss :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → [IsLocallyNoetherian X] →
    (F : X.Modules) → Modules.associatedPoints F = F.weakAss)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_associatedPoints_iff :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → [IsLocallyNoetherian X] →
    (F : X.Modules) → (x : Points X) →
      (x ∈ Modules.associatedPoints F ↔ Modules.etaleStalkWeakAss F x))

/- Definition 71.2.2 (5): if `X` is locally Noetherian, then `x` is an associated
point of `X` if and only if it is a weakly associated point of `X`. -/
@[stacks 0CTX] #check (AlgebraicGeometry.AlgebraicSpace.associatedPoints :
  {S : Scheme.{u}} → (X : AlgebraicSpace S) → [IsLocallyNoetherian X] → Set (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.associatedPoints_eq_weakAss :
  {S : Scheme.{u}} → (X : AlgebraicSpace S) → [IsLocallyNoetherian X] →
    AlgebraicGeometry.AlgebraicSpace.associatedPoints X = X.weakAss)

#check (AlgebraicGeometry.AlgebraicSpace.mem_associatedPoints_iff :
  {S : Scheme.{u}} → (X : AlgebraicSpace S) → [IsLocallyNoetherian X] → (x : Points X) →
    (x ∈ AlgebraicGeometry.AlgebraicSpace.associatedPoints X ↔ x ∈ X.weakAss))
