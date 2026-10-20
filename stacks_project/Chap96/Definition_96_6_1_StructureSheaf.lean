module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.StructureSheaf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Structure sheaf of a category fibred in groupoids

A category fibred in groupoids over `(Sch/S)_fppf` inherits the big fppf structure
sheaf by precomposition with the projection. This is the Stacks inverse image
`𝒪_X = p⁻¹ 𝒪`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

#check (AlgebraicGeometry.GroupoidsOver.inheritedFppfTopology :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S), GrothendieckTopology X.total)

#check (AlgebraicGeometry.GroupoidsOver.inheritedFppfTopology_eq :
  ∀ (X : GroupoidsOver S),
    inheritedFppfTopology X = X.p.inheritedTopology (Scheme.fppfTopology.over S))

#check (AlgebraicGeometry.GroupoidsOver.structureSheaf :
  {S : Scheme.{u}} → (X : GroupoidsOver S) →
    Sheaf (fppfTopology X) RingCat.{u})

#check (AlgebraicGeometry.GroupoidsOver.structureSheaf_def :
  ∀ (X : GroupoidsOver S),
    structureSheaf X =
      (X.p.sheafPushforwardContinuous RingCat.{u}
          (fppfTopology X) (Scheme.fppfTopology.over S)).obj
        (StandardTopology.Big.structureSheaf .fppf S))

#check (AlgebraicGeometry.GroupoidsOver.structureSheaf_obj_eq_big :
  ∀ {X : GroupoidsOver S} (x : X.total),
    (structureSheaf X).obj.obj (op x) =
      (StandardTopology.Big.structureSheaf .fppf S).obj.obj (op (X.p.obj x)))

#check (AlgebraicGeometry.GroupoidsOver.structureSheaf_obj :
  ∀ {X : GroupoidsOver S} (x : X.total),
    (structureSheaf X).obj.obj (op x) = RingCat.of Γ((X.p.obj x).left, ⊤))

#check (AlgebraicGeometry.GroupoidsOver.ringedSite :
  {S : Scheme.{u}} → GroupoidsOver S → RingedSite.{u + 1, u, u})

#check (AlgebraicGeometry.GroupoidsOver.ringedSite_structureSheaf :
  ∀ (X : GroupoidsOver S),
    (ringedSite X).structureSheaf = structureSheaf X)

end AlgebraicGeometry.GroupoidsOver
