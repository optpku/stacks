module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Sites.Sheafification

open CategoryTheory AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {S : Scheme.{u}}

/-- A morphism of set-valued sheaves on the small étale site is a monomorphism
if and only if its map on every geometric stalk is injective. -/
theorem sheafTypeMap_mono_iff_stalk {F G : Sheaf (smallEtaleTopology S) (Type u)}
    (a : F ⟶ G) :
    Mono a ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      Function.Injective
        (ConcreteCategory.hom ((Scheme.pointSmallEtale s).sheafFiber.map a)) := sorry

/-- A morphism of set-valued sheaves on the small étale site is an epimorphism
if and only if its map on every geometric stalk is surjective. -/
theorem sheafTypeMap_epi_iff_stalk {F G : Sheaf (smallEtaleTopology S) (Type u)}
    (a : F ⟶ G) :
    Epi a ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      Function.Surjective
        (ConcreteCategory.hom ((Scheme.pointSmallEtale s).sheafFiber.map a)) := sorry

/-- A short complex of abelian sheaves on the small étale site is exact
if and only if its image on every geometric stalk is exact. -/
theorem sheafAbelian_exact_iff_stalk
    (C : ShortComplex (Sheaf (smallEtaleTopology S) AddCommGrpCat.{u})) :
    C.Exact ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      (((Scheme.pointSmallEtale s).sheafFiber : _ ⥤ AddCommGrpCat.{u}).mapShortComplex.obj C).Exact := sorry

end AlgebraicGeometry.Scheme.Etale
