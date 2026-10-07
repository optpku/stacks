module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport.Components

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/- Lemma 42.10.1 (1): The irreducible components of the support of a coherent module
on a scheme locally of finite type over a universally catenary base are locally finite. -/
@[stacks 02QW] #check
  (AlgebraicGeometry.Scheme.Modules.locallyFinite_irreducibleComponents_moduleSupport :
    ∀ {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
      (δ : S → ℤ) [IsDimensionFunction δ] (F : X.Modules) [F.IsCoherent],
    LocallyFinite fun W : irreducibleComponents
        (AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport F).subscheme ↦
      (AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport F).subschemeι.base ''
        (W : Set (AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport F).subscheme))

/- Lemma 42.10.1 (2): At the generic point of an irreducible component of the
support of a coherent module, the stalk has finite length over the ambient local ring. -/
@[stacks 02QW] #check
  (AlgebraicGeometry.Scheme.Modules.stalk_length_lt_top_at_genericPoint_moduleSupport :
    ∀ {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
      (δ : S → ℤ) [IsDimensionFunction δ] (F : X.Modules) [F.IsCoherent]
      (ξ : genericPoints
        (AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport F).subscheme),
    Module.length
      (X.presheaf.stalk
        ((AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport F).subschemeι ξ.1))
      (RingedSpace.stalkModuleCat F
        ((AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport F).subschemeι ξ.1)) < ⊤)

/- Lemma 42.10.1 (3): A support point attaining an upper bound for the
`δ`-dimension of the support is a generic point of an irreducible component. -/
@[stacks 02QW] #check
  (AlgebraicGeometry.Scheme.Modules.mem_genericPoints_moduleSupport_of_deltaDimension_le :
    ∀ {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
      (δ : S → ℤ) [IsDimensionFunction δ] (F : X.Modules) [F.IsCoherent]
      (k : ℤ)
      (hdim : f.closedSubschemeDeltaDimension δ
        (AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport F) ≤ (k : EInt))
      (ξ : (AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport F).subscheme)
      (hξ : f.relativeDimensionFunction δ
        ((AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport F).subschemeι ξ) = k),
    ξ ∈ genericPoints
      (AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport F).subscheme)
