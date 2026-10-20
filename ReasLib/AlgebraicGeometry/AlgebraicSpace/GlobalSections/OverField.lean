/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Field.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Global sections of algebraic spaces over a field

The ring `Γ(X, 𝒪_X)` of an algebraic space over `Spec k` carries a canonical
`k`-algebra structure, obtained by lifting the atlas structure morphism through
the presentation equalizer.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k)))

/-- The structure morphism of an algebraic space over `Spec k` induces the canonical map
`k → Γ(X, 𝒪_X)`. -/
noncomputable abbrev globalSectionsMap : k →+* globalSectionsRing X :=
  Hom.globalSectionsMap (SchemeRealization.toBase X)

/-- The canonical `k`-algebra structure on `Γ(X, 𝒪_X)`. -/
instance instAlgebra_globalSectionsRing : Algebra k (globalSectionsRing X) :=
  (globalSectionsMap X).toAlgebra

/-- The bundled `k`-algebra of global sections of an algebraic space over `Spec k`. -/
noncomputable def globalSectionsAlg : CommAlgCat k :=
  CommAlgCat.of k (globalSectionsRing X)

/-- The carrier of `globalSectionsAlg X` is `Γ(X, 𝒪_X)`. -/
theorem coe_globalSectionsAlg : (globalSectionsAlg X : Type u) = globalSectionsRing X :=
  rfl

/-- The algebra map into the bundled global-sections algebra. -/
noncomputable abbrev globalSectionsAlgMap : k →+* globalSectionsAlg X :=
  globalSectionsMap X

/-- The bundled algebra map is the unbundled global-sections map. -/
theorem globalSectionsAlgMap_eq : globalSectionsAlgMap X = globalSectionsMap X :=
  rfl

/-- The affine morphism `Spec Γ(X, 𝒪_X) ⟶ Spec k` induced by `globalSectionsMap X`. -/
noncomputable abbrev globalSectionsSpecMap :
    Spec (globalSectionsRing X) ⟶ Spec (of k) :=
  Spec.map (ofHom (globalSectionsMap X))

/-- `globalSectionsSpecMap X` is `Spec.map` of the canonical algebra map `k → Γ(X, 𝒪_X)`. -/
theorem globalSectionsSpecMap_eq :
    globalSectionsSpecMap X = Spec.map (ofHom (algebraMap k (globalSectionsRing X))) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace

