module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.ReducedRelationClosure.Groupoid
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 40.11.8: if the object scheme of a groupoid scheme is the spectrum of a perfect
field, the reduced closed subscheme supported on the closure of the image of `(t, s)` is the
arrow scheme of a groupoid over the same base. -/
@[stacks 04QC]
#check
  (@AlgebraicGeometry.GroupoidScheme.reducedRelationClosure.{u} :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
      (G : AlgebraicGeometry.GroupoidScheme S)
      (eU : Spec (CommRingCat.of k) ≅ G.U.left),
      AlgebraicGeometry.GroupoidScheme S)

#check
  (@AlgebraicGeometry.GroupoidScheme.reducedRelationClosure_U.{u} :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
      (G : AlgebraicGeometry.GroupoidScheme S)
      (eU : Spec (CommRingCat.of k) ≅ G.U.left),
      (AlgebraicGeometry.GroupoidScheme.reducedRelationClosure G eU).U = G.U)

#check
  (@AlgebraicGeometry.GroupoidScheme.reducedRelationClosure_R.{u} :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
      (G : AlgebraicGeometry.GroupoidScheme S)
      (eU : Spec (CommRingCat.of k) ≅ G.U.left),
      (AlgebraicGeometry.GroupoidScheme.reducedRelationClosure G eU).R =
        Scheme.Hom.reducedImageClosureOver
          (AlgebraicGeometry.GroupoidScheme.toPair G).arrow)

#check
  (@AlgebraicGeometry.GroupoidScheme.reducedRelationClosure_s.{u} :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
      (G : AlgebraicGeometry.GroupoidScheme S)
      (eU : Spec (CommRingCat.of k) ≅ G.U.left),
      (AlgebraicGeometry.GroupoidScheme.reducedRelationClosure G eU).s =
        Scheme.Hom.reducedImageClosureιOver
            (AlgebraicGeometry.GroupoidScheme.toPair G).arrow ≫
          (AlgebraicGeometry.GroupoidScheme.pair G.U).s)

#check
  (@AlgebraicGeometry.GroupoidScheme.reducedRelationClosure_t.{u} :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
      (G : AlgebraicGeometry.GroupoidScheme S)
      (eU : Spec (CommRingCat.of k) ≅ G.U.left),
      (AlgebraicGeometry.GroupoidScheme.reducedRelationClosure G eU).t =
        Scheme.Hom.reducedImageClosureιOver
            (AlgebraicGeometry.GroupoidScheme.toPair G).arrow ≫
          (AlgebraicGeometry.GroupoidScheme.pair G.U).t)

#check
  (@AlgebraicGeometry.GroupoidScheme.reducedRelationClosure_c.{u} :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
      (G : AlgebraicGeometry.GroupoidScheme S)
      (eU : Spec (CommRingCat.of k) ≅ G.U.left),
      (AlgebraicGeometry.GroupoidScheme.reducedRelationClosure G eU).c =
        AlgebraicGeometry.GroupoidScheme.Hom.reducedImageClosureCompositionLift
          eU (AlgebraicGeometry.GroupoidScheme.toPair_object_eq G)
          (AlgebraicGeometry.GroupoidScheme.toPair G)
          (AlgebraicGeometry.GroupoidScheme.toPair_isIdentityOnObjects G))

#check
  (@AlgebraicGeometry.GroupoidScheme.reducedRelationClosure_e.{u} :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
      (G : AlgebraicGeometry.GroupoidScheme S)
      (eU : Spec (CommRingCat.of k) ≅ G.U.left),
      (AlgebraicGeometry.GroupoidScheme.reducedRelationClosure G eU).e =
        AlgebraicGeometry.GroupoidScheme.Hom.reducedImageClosureIdentity
          eU (AlgebraicGeometry.GroupoidScheme.toPair_object_eq G)
          (AlgebraicGeometry.GroupoidScheme.toPair G)
          (AlgebraicGeometry.GroupoidScheme.toPair_isIdentityOnObjects G))

#check
  (@AlgebraicGeometry.GroupoidScheme.reducedRelationClosure_i.{u} :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
      (G : AlgebraicGeometry.GroupoidScheme S)
      (eU : Spec (CommRingCat.of k) ≅ G.U.left),
      (AlgebraicGeometry.GroupoidScheme.reducedRelationClosure G eU).i =
        AlgebraicGeometry.GroupoidScheme.Hom.reducedImageClosureInverse
          (AlgebraicGeometry.GroupoidScheme.toPair_object_eq G)
          (AlgebraicGeometry.GroupoidScheme.toPair G)
          (AlgebraicGeometry.GroupoidScheme.toPair_isIdentityOnObjects G))

end AlgebraicGeometry.GroupoidScheme
