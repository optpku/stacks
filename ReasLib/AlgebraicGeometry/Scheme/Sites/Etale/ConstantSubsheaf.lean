/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Topology.Sober

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- On an irreducible scheme, an inclusion of a constant sheaf of sets into a subsheaf
of a larger constant sheaf is an isomorphism if its geometric generic stalk map is
an isomorphism. -/
theorem isIso_of_genericStalk_types
    (X : Scheme.{u}) [IrreducibleSpace X]
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (geometricPoint : Spec (.of Ω) ⟶ X)
    (hη : IsGenericPoint (geometricPoint default) Set.univ)
    (S' S : Type u) (ι : S' ⟶ S) [Mono ι]
    (G : Sheaf X.smallEtaleTopology (Type u))
    (h_lower : (constantSheaf X.smallEtaleTopology (Type u)).obj S' ⟶ G)
    [Mono h_lower]
    (h_upper : G ⟶ (constantSheaf X.smallEtaleTopology (Type u)).obj S)
    [Mono h_upper]
    (h_factor : h_lower ≫ h_upper =
      (constantSheaf X.smallEtaleTopology (Type u)).map ι)
    [IsIso ((Scheme.pointSmallEtale geometricPoint).sheafFiber.map h_lower)] :
    IsIso h_lower := sorry

/-- On an irreducible scheme, an inclusion of a constant sheaf of abelian groups into
a subsheaf of a larger constant sheaf is an isomorphism if its geometric generic stalk
map is an isomorphism. -/
theorem isIso_of_genericStalk_addCommGrp
    (X : Scheme.{u}) [IrreducibleSpace X]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (geometricPoint : Spec (.of Ω) ⟶ X)
    (hη : IsGenericPoint (geometricPoint default) Set.univ)
    (A' A : AddCommGrpCat.{u}) (ι : A' ⟶ A) [Mono ι]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (h_lower : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A' ⟶ G)
    [Mono h_lower]
    (h_upper : G ⟶ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A)
    [Mono h_upper]
    (h_factor : h_lower ≫ h_upper =
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map ι)
    [IsIso ((Scheme.pointSmallEtale geometricPoint).sheafFiber.map h_lower)] :
    IsIso h_lower := sorry

/-- On an irreducible scheme, an inclusion of a constant sheaf of modules over a ring
into a subsheaf of a larger constant sheaf is an isomorphism if its geometric generic
stalk map is an isomorphism. -/
theorem isIso_of_genericStalk_module
    (X : Scheme.{u}) [IrreducibleSpace X]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (geometricPoint : Spec (.of Ω) ⟶ X)
    (hη : IsGenericPoint (geometricPoint default) Set.univ)
    (Λ : Type u) [Ring Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    (M' M : ModuleCat.{u} Λ) (ι : M' ⟶ M) [Mono ι]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (h_lower : (constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).obj M' ⟶ G)
    [Mono h_lower]
    (h_upper : G ⟶ (constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).obj M)
    [Mono h_upper]
    (h_factor : h_lower ≫ h_upper =
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).map ι)
    [IsIso ((Scheme.pointSmallEtale geometricPoint).sheafFiber.map h_lower)] :
    IsIso h_lower := sorry

end AlgebraicGeometry.Scheme.Etale
