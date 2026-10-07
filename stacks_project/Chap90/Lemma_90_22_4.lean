module

public import stacks_project.Chap90.Definition_90_22_1_Prorepresentable
public import stacks_project.Chap90.Definition_90_22_2_Completion

/-!
# Prorepresentable groupoids in functors versus completion and object/arrow functors

A groupoid in functors on `ArtinianLocalAlgCat` is prorepresentable if and only if its
completion is representable as a groupoid in functors on `CompleteLocalAlgCat`, and if
and only if its object and arrow functors are prorepresentable.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

variable {G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)}

/-- Lemma 90.22.4 (1): a groupoid in functors `G` on `ArtinianLocalAlgCat Λ k` is
`IsProrepresentable` if and only if `completion G` is `IsRepresentable` as a groupoid in
functors on `CompleteLocalAlgCat Λ k`. -/
@[stacks 06KG]
theorem isProrepresentable_iff_isRepresentable_completion
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)) :
    IsProrepresentable G ↔ IsRepresentable (completion G) :=
  sorry

/-- Lemma 90.22.4 (2): a groupoid in functors `G` on `ArtinianLocalAlgCat Λ k` is
`IsProrepresentable` if and only if the set-valued functors `G.U` and `G.R` are
`Functor.IsProrepresentable`. -/
@[stacks 06KG]
theorem isProrepresentable_iff_obj_arrow
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)) :
    IsProrepresentable G ↔ Functor.IsProrepresentable G.U ∧ Functor.IsProrepresentable G.R :=
  sorry

/-- The completion of a prorepresentable groupoid in functors is representable. -/
instance instIsRepresentable_completion [IsProrepresentable G] :
    IsRepresentable (completion G) :=
  sorry

/-- A groupoid in functors whose completion is representable is prorepresentable. -/
instance instIsProrepresentable_of_isRepresentable_completion
    [IsRepresentable (completion G)] : IsProrepresentable G :=
  sorry

/-- The object functor of a prorepresentable groupoid in functors is prorepresentable. -/
instance instFunctorIsProrepresentable_obj [IsProrepresentable G] :
    Functor.IsProrepresentable G.U :=
  sorry

/-- The arrow functor of a prorepresentable groupoid in functors is prorepresentable. -/
instance instFunctorIsProrepresentable_arrow [IsProrepresentable G] :
    Functor.IsProrepresentable G.R :=
  sorry

/-- A groupoid in functors whose object and arrow functors are prorepresentable is
prorepresentable. -/
instance instIsProrepresentable_of_functorIsProrepresentable
    [Functor.IsProrepresentable G.U] [Functor.IsProrepresentable G.R] :
    IsProrepresentable G :=
  sorry

end CategoryTheory.GroupoidInFunctors
