/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tor.Regular
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 43.14.2 (1): the Tor sheaves of two coherent modules on a nonsingular variety are coherent. -/
@[stacks 0AZT] #check
  (AlgebraicGeometry.SchemeOverField.tor_isCoherent :
    ∀ {k : Type u} [Field k]
      (X : AlgebraicGeometry.SchemeOverField k) [Variety X] [Scheme.Regular X.left]
      [RingedSpace.ModuleDerived.Tensor.Has X.left.toRingedSpace]
      (F G : X.left.Modules) [F.IsCoherent] [G.IsCoherent] (p : ℕ),
      (RingedSpace.ModuleDerived.tor p F G).IsCoherent)

/- Lemma 43.14.2 (2): the stalk of the Tor sheaf is isomorphic to Tor of the two stalk modules over the local ring. -/
@[stacks 0AZT] #check
  (AlgebraicGeometry.SchemeOverField.stalkTor_isomorphic :
    ∀ {k : Type u} [Field k]
      (X : AlgebraicGeometry.SchemeOverField k) [Variety X] [Scheme.Regular X.left]
      [RingedSpace.ModuleDerived.Tensor.Has X.left.toRingedSpace]
      (F G : X.left.Modules) [F.IsCoherent] [G.IsCoherent] (p : ℕ) (x : X.left),
      IsIsomorphic
        (RingedSpace.stalkModuleCat (RingedSpace.ModuleDerived.tor p F G) x)
        (ModuleCat.Tor.obj p (RingedSpace.stalkModuleCat F x)
          (RingedSpace.stalkModuleCat G x)))

/- Lemma 43.14.2 (3): the support of a Tor sheaf is contained in the intersection of the supports of its two arguments. -/
@[stacks 0AZT] #check
  (AlgebraicGeometry.SchemeOverField.moduleSupport_tor_subset :
    ∀ {k : Type u} [Field k]
      (X : AlgebraicGeometry.SchemeOverField k) [Variety X] [Scheme.Regular X.left]
      [RingedSpace.ModuleDerived.Tensor.Has X.left.toRingedSpace]
      (F G : X.left.Modules) [F.IsCoherent] [G.IsCoherent] (p : ℕ),
      RingedSpace.moduleSupport (RingedSpace.ModuleDerived.tor p F G) ⊆
        RingedSpace.moduleSupport F ∩ RingedSpace.moduleSupport G)

/- Lemma 43.14.2 (4): Tor vanishes in every degree strictly larger than the dimension of the nonsingular variety. -/
@[stacks 0AZT] #check
  (AlgebraicGeometry.SchemeOverField.tor_isZero_of_dimension_lt :
    ∀ {k : Type u} [Field k]
      (X : AlgebraicGeometry.SchemeOverField k) [Variety X] [Scheme.Regular X.left]
      [RingedSpace.ModuleDerived.Tensor.Has X.left.toRingedSpace]
      (F G : X.left.Modules) [F.IsCoherent] [G.IsCoherent] (p : ℕ)
      (hp : topologicalKrullDim X.left < (p : WithBot ℕ∞)),
      IsZero (RingedSpace.ModuleDerived.tor p F G))

end AlgebraicGeometry.SchemeOverField
