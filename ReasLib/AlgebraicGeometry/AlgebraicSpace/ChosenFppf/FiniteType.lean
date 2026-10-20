module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- A morphism of sheaves on `(Sch/S)_fppf` is locally of finite type in the
algebraic-space sense when every commutative square against it with étale
vertical arrows from sheafified representables has locally-of-finite-type top
arrow. This does not require the morphism to be representable by schemes. -/
def locallyOfFiniteTypeOnEtaleSquares {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) : Prop :=
  ∀ {U V : 𝒮.bigSite S}
    (a : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
    (b : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ Y) (h : U ⟶ V),
    relativelyEtale a → relativelyEtale b →
      a ≫ f = (𝒮.bigTopology S).sheafifiedRepresentableMap h ≫ b →
        LocallyOfFiniteType ((𝒮.bigToScheme S).map h)

/-- Algebraic-space local finite type unpacks as local finite type of the top
arrow of every étale scheme square. -/
theorem locallyOfFiniteTypeOnEtaleSquares_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) :
    locallyOfFiniteTypeOnEtaleSquares f ↔
      ∀ {U V : 𝒮.bigSite S}
        (a : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
        (b : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ Y) (h : U ⟶ V),
        relativelyEtale a → relativelyEtale b →
          a ≫ f = (𝒮.bigTopology S).sheafifiedRepresentableMap h ≫ b →
            LocallyOfFiniteType ((𝒮.bigToScheme S).map h) :=
  sorry

/-- Algebraic-space local finite type implies local finite type of the top
arrow of any étale scheme square. -/
theorem locallyOfFiniteTypeOnEtaleSquares_spec {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} {f : X ⟶ Y}
    (hf : locallyOfFiniteTypeOnEtaleSquares f) {U V : 𝒮.bigSite S}
    (a : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
    (b : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ Y) (h : U ⟶ V)
    (ha : relativelyEtale a) (hb : relativelyEtale b)
    (hsq : a ≫ f = (𝒮.bigTopology S).sheafifiedRepresentableMap h ≫ b) :
    LocallyOfFiniteType ((𝒮.bigToScheme S).map h) :=
  sorry


end AlgebraicGeometry
end
