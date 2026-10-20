module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection

/-!
# Structure sheaves on associated sites

The projection of a category fibred in groupoids pulls the big structure sheaf
back by continuous precomposition for each standard topology.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The structure sheaf `𝒪_𝒳` on the associated `τ`-site of a category fibred
in groupoids, obtained by continuous precomposition of the big `τ`-structure
sheaf of `S` with the projection. -/
def associatedStructureSheaf (𝒳 : GroupoidsOver S) (τ : StandardTopology) :
    Sheaf (𝒳.associatedTopology τ) RingCat.{u} :=
  (𝒳.p.sheafPushforwardContinuous RingCat.{u}
      (𝒳.associatedTopology τ) (τ.overTopology S)).obj
    (StandardTopology.Big.structureSheaf τ S)

/-- Sections of `𝒪_𝒳` at `x` agree with sections of the big `τ`-structure sheaf
at `p(x)`. -/
theorem associatedStructureSheaf_obj_eq_big {𝒳 : GroupoidsOver S}
    (τ : StandardTopology) (x : 𝒳.total) :
    (associatedStructureSheaf 𝒳 τ).obj.obj (op x) =
      (StandardTopology.Big.structureSheaf τ S).obj.obj (op (𝒳.p.obj x)) :=
  sorry

/-- For an object `x` of `𝒳` lying over `U`, the value of `𝒪_𝒳` at `x` is
`Γ(U, 𝒪_U)`. -/
theorem associatedStructureSheaf_obj {𝒳 : GroupoidsOver S}
    (τ : StandardTopology) (x : 𝒳.total) :
    (associatedStructureSheaf 𝒳 τ).obj.obj (op x) =
      RingCat.of Γ((𝒳.p.obj x).left, ⊤) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
