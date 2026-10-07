module

public import stacks_project.Chap90.Definition_90_21_1_Groupoid
public import stacks_project.Chap90.Definition_90_22_2_TypesCompletion

/-!
# Completion of a groupoid in functors

The completion of a groupoid in functors on `ArtinianLocalAlgCat` is the groupoid in
functors on `CompleteLocalAlgCat` obtained by completing the object and arrow functors
and the structure maps, transporting composition along the canonical pullback
comparison for set-valued completion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- The completion of a groupoid in functors on `ArtinianLocalAlgCat Λ k`, obtained by
completing the object and arrow functors and the structure maps, and transporting
composition along `Functor.typesCompletionPullbackIso`. -/
def completion (G : GroupoidInFunctors (ArtinianLocalAlgCat Λ k)) :
    GroupoidInFunctors (CompleteLocalAlgCat Λ k) where
  U := Functor.typesCompletion G.U
  R := Functor.typesCompletion G.R
  s := Functor.typesCompletionMap G.s
  t := Functor.typesCompletionMap G.t
  c := (Functor.typesCompletionPullbackIso G.s G.t).inv ≫ Functor.typesCompletionMap G.c
  e := Functor.typesCompletionMap G.e
  i := Functor.typesCompletionMap G.i
  comp_source := sorry
  comp_target := sorry
  identity_source := sorry
  identity_target := sorry
  inverse_source := sorry
  inverse_target := sorry
  associativity := sorry
  right_identity := sorry
  left_identity := sorry
  inverse_comp := sorry
  comp_inverse := sorry

/-- Completion of a groupoid in functors completes the object functor. -/
theorem completion_U (G : GroupoidInFunctors (ArtinianLocalAlgCat Λ k)) :
    (completion G).U = Functor.typesCompletion G.U :=
  sorry

/-- Completion of a groupoid in functors completes the arrow functor. -/
theorem completion_R (G : GroupoidInFunctors (ArtinianLocalAlgCat Λ k)) :
    (completion G).R = Functor.typesCompletion G.R :=
  sorry

/-- Completion of a groupoid in functors completes the source map. -/
theorem completion_s (G : GroupoidInFunctors (ArtinianLocalAlgCat Λ k)) :
    (completion G).s = Functor.typesCompletionMap G.s :=
  sorry

/-- Completion of a groupoid in functors completes the target map. -/
theorem completion_t (G : GroupoidInFunctors (ArtinianLocalAlgCat Λ k)) :
    (completion G).t = Functor.typesCompletionMap G.t :=
  sorry

/-- Completion of composition is the completed composition, transported by the inverse of
`Functor.typesCompletionPullbackIso`. -/
theorem completion_c (G : GroupoidInFunctors (ArtinianLocalAlgCat Λ k)) :
    (completion G).c =
      (Functor.typesCompletionPullbackIso G.s G.t).inv ≫ Functor.typesCompletionMap G.c :=
  sorry

/-- Completion of a groupoid in functors completes the identity-arrow map. -/
theorem completion_e (G : GroupoidInFunctors (ArtinianLocalAlgCat Λ k)) :
    (completion G).e = Functor.typesCompletionMap G.e :=
  sorry

/-- Completion of a groupoid in functors completes the inverse-arrow map. -/
theorem completion_i (G : GroupoidInFunctors (ArtinianLocalAlgCat Λ k)) :
    (completion G).i = Functor.typesCompletionMap G.i :=
  sorry

/-- The completed groupoid in functors is the source quintuple `(U, R, s, t, c)` together
with the identity and inverse maps, with object and arrow functors completed by
`Functor.typesCompletion` and structure maps completed by `Functor.typesCompletionMap`,
and with composition transported by the inverse of `Functor.typesCompletionPullbackIso`. -/
theorem completion_spec (G : GroupoidInFunctors (ArtinianLocalAlgCat Λ k)) :
    (completion G).U = Functor.typesCompletion G.U ∧
      (completion G).R = Functor.typesCompletion G.R ∧
      (completion G).s = Functor.typesCompletionMap G.s ∧
      (completion G).t = Functor.typesCompletionMap G.t ∧
      (completion G).c =
        (Functor.typesCompletionPullbackIso G.s G.t).inv ≫
          Functor.typesCompletionMap G.c ∧
      (completion G).e = Functor.typesCompletionMap G.e ∧
      (completion G).i = Functor.typesCompletionMap G.i :=
  sorry

end CategoryTheory.GroupoidInFunctors
