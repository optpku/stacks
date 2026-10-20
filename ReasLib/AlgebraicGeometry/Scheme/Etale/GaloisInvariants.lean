module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.StalkGaloisSet
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.GroupTheory.GroupAction.Defs

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

/-- The stalk germ of a global étale section is fixed by the residue-field Galois action. -/
theorem globalSectionsToEtaleStalk_mem_fixedPoints (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u))
    (x : F.obj.obj (op (MorphismProperty.Over.mk _ (𝟙 (Spec (.of K))) inferInstance))) :
    globalSectionsToEtaleStalk K s F x ∈
      MulAction.fixedPoints s.absoluteGaloisGroup
        (ToType ((stalkGaloisSet K s).obj F).obj.obj) := sorry

/-- Global étale sections map to Galois-invariant stalk germs. -/
noncomputable def globalSectionsToGaloisInvariants (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u))
    (x : F.obj.obj (op (MorphismProperty.Over.mk _ (𝟙 (Spec (.of K))) inferInstance))) :
    MulAction.fixedPoints s.absoluteGaloisGroup
      (ToType ((stalkGaloisSet K s).obj F).obj.obj) :=
  ⟨globalSectionsToEtaleStalk K s F x,
    globalSectionsToEtaleStalk_mem_fixedPoints K s F x⟩

/-- The underlying value of a Galois-invariant global-section germ is its canonical stalk germ. -/
theorem globalSectionsToGaloisInvariants_val (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u))
    (x : F.obj.obj (op (MorphismProperty.Over.mk _ (𝟙 (Spec (.of K))) inferInstance))) :
    (globalSectionsToGaloisInvariants K s F x).val =
      globalSectionsToEtaleStalk K s F x := rfl

/-- The canonical map from global étale sections to Galois-fixed stalk germs is bijective. -/
theorem globalSectionsToGaloisInvariants_bijective
    (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)) :
    Function.Bijective (globalSectionsToGaloisInvariants K s F) := sorry

/-- The canonical map to Galois-invariant stalk germs commutes with morphisms of étale sheaves. -/
theorem globalSectionsToGaloisInvariants_natural
    (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)} (f : F ⟶ G)
    (x : F.obj.obj
      (op (MorphismProperty.Over.mk _ (𝟙 (Spec (.of K))) inferInstance))) :
    ((globalSectionsToGaloisInvariants K s G)
        (f.hom.app
          (op (MorphismProperty.Over.mk _ (𝟙 (Spec (.of K))) inferInstance)) x) :
        ToType ((stalkGaloisSet K s).obj G).obj.obj) =
      ConcreteCategory.hom ((stalkGaloisSet K s).map f).hom.hom.hom
        ((globalSectionsToGaloisInvariants K s F) x) := sorry

end AlgebraicGeometry.Scheme.Etale
