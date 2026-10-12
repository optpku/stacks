/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection
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

/-- The Grothendieck topology on the total category of a category fibred in
groupoids, inherited from `(Sch/S)_fppf`. -/
abbrev inheritedFppfTopology (X : GroupoidsOver S) :
    GrothendieckTopology X.total :=
  X.p.inheritedTopology (Scheme.fppfTopology.over S)

/-- `inheritedFppfTopology` is the topology inherited along the projection from
the big fppf site of `S`. -/
theorem inheritedFppfTopology_eq (X : GroupoidsOver S) :
    inheritedFppfTopology X = X.p.inheritedTopology (Scheme.fppfTopology.over S) :=
  sorry

/-- The structure sheaf `𝒪_X` of a category fibred in groupoids over
`(Sch/S)_fppf`, obtained as the inverse image `p⁻¹ 𝒪` of the big fppf
structure sheaf. -/
def structureSheaf (X : GroupoidsOver S) :
    Sheaf (inheritedFppfTopology X) RingCat.{u} :=
  (X.p.sheafPushforwardContinuous RingCat.{u}
      (inheritedFppfTopology X) (Scheme.fppfTopology.over S)).obj
    (StandardTopology.Big.structureSheaf .fppf S)

/-- `𝒪_X` is the continuous pushforward of the big fppf structure sheaf along
the projection of `X`. -/
theorem structureSheaf_def (X : GroupoidsOver S) :
    structureSheaf X =
      (X.p.sheafPushforwardContinuous RingCat.{u}
          (inheritedFppfTopology X) (Scheme.fppfTopology.over S)).obj
        (StandardTopology.Big.structureSheaf .fppf S) :=
  sorry

/-- Sections of `𝒪_X` at `x` agree with sections of the big fppf structure sheaf
at `p(x)`. -/
theorem structureSheaf_obj_eq_big {X : GroupoidsOver S} (x : X.total) :
    (structureSheaf X).obj.obj (op x) =
      (StandardTopology.Big.structureSheaf .fppf S).obj.obj (op (X.p.obj x)) :=
  sorry

/-- For an object `x` of `X` lying over `U`, the value of `𝒪_X` at `x` is
`Γ(U, 𝒪_U)`. -/
theorem structureSheaf_obj {X : GroupoidsOver S} (x : X.total) :
    (structureSheaf X).obj.obj (op x) = RingCat.of Γ((X.p.obj x).left, ⊤) :=
  sorry

/-- The fppf ringed site of `X`, with structure sheaf `𝒪_X`. -/
abbrev ringedSite (X : GroupoidsOver S) :=
  RingedSite.ofRingSheaf (inheritedFppfTopology X) (structureSheaf X)

/-- The structure sheaf of `ringedSite X` is `𝒪_X`. -/
theorem ringedSite_structureSheaf (X : GroupoidsOver S) :
    (ringedSite X).structureSheaf = structureSheaf X :=
  sorry

end AlgebraicGeometry.GroupoidsOver
