/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.GroupTheory.GroupAction.Defs
public import stacks_project.Chap59.Theorem_59_56_3_StalkFunctor

open CategoryTheory Opposite AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Restriction of a global étale section along the geometric point, as a
stalk germ. -/
noncomputable def globalSectionsToEtaleStalk (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)) :
    F.obj.obj (op (MorphismProperty.Over.mk _ (𝟙 (Spec (.of K))) inferInstance)) →
      (etalePoint K s).presheafFiber.obj F.1 :=
  (etalePoint K s).toPresheafFiber
    (MorphismProperty.Over.mk _ (𝟙 (Spec (.of K))) inferInstance)
    (Over.homMk (geometricPointHom K s)) F.1

/-- Global étale sections map to Galois-invariant stalk germs. -/
noncomputable def globalSectionsToGaloisInvariants (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u))
    (x : F.obj.obj (op (MorphismProperty.Over.mk _ (𝟙 (Spec (.of K))) inferInstance))) :
    MulAction.fixedPoints s.absoluteGaloisGroup
      (ToType ((stalkGaloisSet K s).obj F).obj.obj) :=
  ⟨globalSectionsToEtaleStalk K s F x, sorry⟩

/-- Lemma 59.56.5: under the assumptions of Theorem 59.56.3, for a sheaf of
sets `F` on the small étale site of `S = Spec K` there is a functorial
bijection `Γ(S, F) ≃ (F_s̄)^G` between global étale sections and Galois
invariants of the stalk at `s̄`. -/
@[stacks 04JM]
noncomputable def globalSectionsEquivGaloisInvariants
    (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)) :
    F.obj.obj (op (MorphismProperty.Over.mk _ (𝟙 (Spec (.of K))) inferInstance)) ≃
      MulAction.fixedPoints s.absoluteGaloisGroup
        (ToType ((stalkGaloisSet K s).obj F).obj.obj) :=
  Equiv.ofBijective (globalSectionsToGaloisInvariants K s F) sorry

/-- Naturality of `globalSectionsEquivGaloisInvariants` in morphisms of
étale sheaves of sets. -/
theorem globalSectionsEquivGaloisInvariants_natural
    (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)} (f : F ⟶ G)
    (x : F.obj.obj
      (op (MorphismProperty.Over.mk _ (𝟙 (Spec (.of K))) inferInstance))) :
    ((globalSectionsEquivGaloisInvariants K s G)
        (f.hom.app
          (op (MorphismProperty.Over.mk _ (𝟙 (Spec (.of K))) inferInstance)) x) :
        ToType ((stalkGaloisSet K s).obj G).obj.obj) =
      ConcreteCategory.hom ((stalkGaloisSet K s).map f).hom.hom.hom
        ((globalSectionsEquivGaloisInvariants K s F) x) := sorry

end AlgebraicGeometry.Scheme.Etale
