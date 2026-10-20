/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.GaloisInvariants
import StacksCheckRecall

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

@[expose] public section

universe u

open AlgebraicGeometry.Scheme.Etale

/- Lemma 59.56.5: global sections of an étale sheaf on a field spectrum are
in functorial bijection with the Galois invariants of its geometric stalk. -/
@[stacks 04JM] #check
  (AlgebraicGeometry.Scheme.Etale.globalSectionsToGaloisInvariants_bijective :
    ∀ (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
      (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)),
      Function.Bijective (globalSectionsToGaloisInvariants K s F))

#check (AlgebraicGeometry.Scheme.Etale.globalSectionsToGaloisInvariants_natural :
  ∀ (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)} (f : F ⟶ G)
    (x : F.obj.obj
      (op (MorphismProperty.Over.mk _ (𝟙 (Spec (.of K))) inferInstance))),
    ((globalSectionsToGaloisInvariants K s G)
        (f.hom.app
          (op (MorphismProperty.Over.mk _ (𝟙 (Spec (.of K))) inferInstance)) x) :
        ToType ((stalkGaloisSet K s).obj G).obj.obj) =
      ConcreteCategory.hom ((stalkGaloisSet K s).map f).hom.hom.hom
        ((globalSectionsToGaloisInvariants K s F) x))
