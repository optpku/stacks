/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.GroupCohomology.Nonabelian

@[expose] public section

universe u v

variable {G : Type u} {A : Type v} [Group G] [Group A] [MulDistribMulAction G A]

open scoped MatrixGroups

/- The non-abelian cohomology API remains available through this import path. -/
#check (GroupCohomology.NonabelianCocycle (G := G) (A := A) : Type (max u v))

#check (GroupCohomology.NonabelianCohomologous :
  GroupCohomology.NonabelianCocycle (G := G) (A := A) →
    GroupCohomology.NonabelianCocycle (G := G) (A := A) → Prop)

#check (GroupCohomology.nonabelianCohomologous_equivalence :
  Equivalence (GroupCohomology.NonabelianCohomologous (G := G) (A := A)))

#check (GroupCohomology.nonabelianH1 (G := G) (A := A) : Type (max u v))

#check (GroupCohomology.NonabelianCocycle.class :
  GroupCohomology.NonabelianCocycle (G := G) (A := A) →
    GroupCohomology.nonabelianH1 (G := G) (A := A))

#check (GroupCohomology.NonabelianCocycle.class_eq_iff :
  ∀ c₁ c₂ : GroupCohomology.NonabelianCocycle (G := G) (A := A),
    c₁.class = c₂.class ↔ GroupCohomology.NonabelianCohomologous c₁ c₂)

variable [TopologicalSpace G]

#check (GroupCohomology.NonabelianCocycle.IsContinuous :
  GroupCohomology.NonabelianCocycle (G := G) (A := A) → Prop)

#check (GroupCohomology.ContinuousNonabelianCocycle (G := G) (A := A) : Type (max u v))

#check (GroupCohomology.ContinuousNonabelianCocycle.isContinuous :
  ∀ c : GroupCohomology.ContinuousNonabelianCocycle (G := G) (A := A), c.1.IsContinuous)

#check (GroupCohomology.ContinuousNonabelianCohomologous :
  GroupCohomology.ContinuousNonabelianCocycle (G := G) (A := A) →
    GroupCohomology.ContinuousNonabelianCocycle (G := G) (A := A) → Prop)

#check (GroupCohomology.continuousNonabelianCohomologous_equivalence :
  Equivalence (GroupCohomology.ContinuousNonabelianCohomologous (G := G) (A := A)))

#check (GroupCohomology.continuousNonabelianH1 (G := G) (A := A) : Type (max u v))

#check (GroupCohomology.ContinuousNonabelianCocycle.class :
  GroupCohomology.ContinuousNonabelianCocycle (G := G) (A := A) →
    GroupCohomology.continuousNonabelianH1 (G := G) (A := A))

#check (GroupCohomology.ContinuousNonabelianCocycle.class_eq_iff :
  ∀ c₁ c₂ : GroupCohomology.ContinuousNonabelianCocycle (G := G) (A := A),
    c₁.class = c₂.class ↔ GroupCohomology.ContinuousNonabelianCohomologous c₁ c₂)

variable {Ksep : Type v} [Field Ksep] {d : ℕ} [MulSemiringAction G Ksep]

#check (GroupCohomology.galoisPGLAction (G := G) (Ksep := Ksep) (d := d) :
  MulDistribMulAction G (PGL(d, Ksep)))

end
