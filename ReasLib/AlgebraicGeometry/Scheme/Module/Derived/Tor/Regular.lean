module

public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tor.Coherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Dimension.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
  (X : AlgebraicGeometry.SchemeOverField k) [Variety X] [Scheme.Regular X.left]
  [RingedSpace.ModuleDerived.Tensor.Has X.left.toRingedSpace]
  (F G : X.left.Modules) [F.IsCoherent] [G.IsCoherent]

/-- Every degree of the Tor sheaf of coherent modules on a regular variety is coherent. -/
@[instance]
theorem tor_isCoherent (p : ℕ) :
    (RingedSpace.ModuleDerived.tor p F G).IsCoherent := sorry

/-- The stalk of a Tor sheaf is isomorphic to the Tor of the corresponding stalk modules. -/
theorem stalkTor_isomorphic (p : ℕ) (x : X.left) :
    IsIsomorphic
      (RingedSpace.stalkModuleCat (RingedSpace.ModuleDerived.tor p F G) x)
      (ModuleCat.Tor.obj p (RingedSpace.stalkModuleCat F x)
        (RingedSpace.stalkModuleCat G x)) := sorry

/-- The support of a Tor sheaf is contained in the intersection of the supports of its arguments. -/
theorem moduleSupport_tor_subset (p : ℕ) :
    RingedSpace.moduleSupport (RingedSpace.ModuleDerived.tor p F G) ⊆
      RingedSpace.moduleSupport F ∩ RingedSpace.moduleSupport G := sorry

/-- Tor vanishes in every degree strictly larger than the dimension of a regular variety. -/
theorem tor_isZero_of_dimension_lt (p : ℕ)
    (hp : topologicalKrullDim X.left < (p : WithBot ℕ∞)) :
    IsZero (RingedSpace.ModuleDerived.tor p F G) := sorry

end AlgebraicGeometry.SchemeOverField
