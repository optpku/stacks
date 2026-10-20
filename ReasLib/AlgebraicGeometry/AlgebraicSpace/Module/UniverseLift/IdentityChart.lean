module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift.LocalHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IdentityChart

/-! # Actual global Hom maps from the identity chart of a represented scheme -/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.IdentityChart

variable {S : Scheme.{u}}

/-- The structural arrow is the actual Yoneda preimage of the chart map. -/
def structuralArrow (T : Over S) (V : smallEtaleSite (ofOver T)) :
    V ⟶ SmallEtaleGlueing.idObj T :=
  MorphismProperty.CostructuredArrow.homMk (yoneda.preimage V.hom) trivial (by sorry)

/-- Unslice a module morphism by evaluating it at every actual structural chart arrow. -/
def homOfSlice (T : Over S) (F G : (ofOver T).Modules)
    (θ : F.over (SmallEtaleGlueing.idObj T) ⟶ G.over (SmallEtaleGlueing.idObj T)) : F ⟶ G :=
  ⟨{ app := fun V ↦ θ.val.app (op (Over.mk (structuralArrow T V.unop)))
     naturality := sorry }⟩

/-- The reverse is the native restriction of the supplied global module morphism. -/
def sliceHomEquiv (T : Over S) (F G : (ofOver T).Modules) :
    (F.over (SmallEtaleGlueing.idObj T) ⟶ G.over (SmallEtaleGlueing.idObj T)) ≃ (F ⟶ G) where
  toFun := homOfSlice T F G
  invFun θ := θ.over (SmallEtaleGlueing.idObj T)
  left_inv := sorry
  right_inv := sorry

/-- An identity-chart internal-Hom section gives the actual global Hom map. The supplied
scheme realization only transports the original data; it supplies no comparison witness. -/
def homEquiv {Z : AlgebraicSpace S} (F G : Z.Modules)
    (T : Over S) (h : Z = ofOver T) :
    ((h ▸ Modules.internalHom F G).val.obj (op (SmallEtaleGlueing.idObj T))) ≃ (F ⟶ G) := by
  subst Z
  exact (Modules.localHomEquiv F G (SmallEtaleGlueing.idObj T)).trans (sliceHomEquiv T F G)

end AlgebraicGeometry.AlgebraicSpace.Modules.IdentityChart
