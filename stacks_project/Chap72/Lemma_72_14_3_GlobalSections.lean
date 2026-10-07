module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Field.Basic
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import stacks_project.Chap69.Situation_69_16_1_GlobalSections

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

/-- The two presentation restrictions agree on the global-sections map of the chosen atlas
structure morphism. -/
theorem globalSectionsMap_equalizes :
    ((Scheme.ΓSpecIso (of k)).inv ≫ (chosenPresentation X).U.hom.appTop) ≫
        (chosenPresentation X).tAppTop =
      ((Scheme.ΓSpecIso (of k)).inv ≫ (chosenPresentation X).U.hom.appTop) ≫
        (chosenPresentation X).sAppTop :=
  sorry

/-- The structure morphism of an algebraic space over `Spec k` induces the `k`-algebra map
`k → Γ(X, 𝒪_X)`. -/
noncomputable def globalSectionsMap : k →+* globalSectionsRing X :=
  (equalizer.lift
      ((Scheme.ΓSpecIso (of k)).inv ≫ (chosenPresentation X).U.hom.appTop)
      (globalSectionsMap_equalizes X)).hom

/-- After comparison with the chosen atlas, `globalSectionsMap X` recovers the scheme-level
global-sections map of the atlas structure morphism. -/
theorem globalSectionsMap_comp_ι :
    (globalSectionsRing_ι X).hom.comp (globalSectionsMap X) =
      Scheme.Hom.globalSectionsMap (chosenPresentation X).U.hom :=
  sorry

/-- The canonical `k`-algebra structure on `Γ(X, 𝒪_X)`. -/
instance instAlgebra_globalSectionsRing : Algebra k (globalSectionsRing X) :=
  (globalSectionsMap X).toAlgebra

/-- The bundled `k`-algebra of global sections of an algebraic space over `Spec k`. -/
noncomputable def globalSectionsAlg : CommAlgCat k :=
  CommAlgCat.of k (globalSectionsRing X)

/-- The carrier of `globalSectionsAlg X` is `Γ(X, 𝒪_X)`. -/
theorem coe_globalSectionsAlg : (globalSectionsAlg X : Type u) = globalSectionsRing X :=
  sorry

/-- The algebra map into the bundled global-sections algebra. -/
noncomputable abbrev globalSectionsAlgMap : k →+* globalSectionsAlg X :=
  globalSectionsMap X

/-- The bundled algebra map is the unbundled global-sections map. -/
theorem globalSectionsAlgMap_eq : globalSectionsAlgMap X = globalSectionsMap X :=
  sorry

/-- The affine morphism `Spec Γ(X, 𝒪_X) ⟶ Spec k` induced by `globalSectionsMap X`. -/
noncomputable abbrev globalSectionsSpecMap :
    Spec (globalSectionsRing X) ⟶ Spec (of k) :=
  Spec.map (ofHom (globalSectionsMap X))

/-- `globalSectionsSpecMap X` is `Spec.map` of the canonical algebra map `k → Γ(X, 𝒪_X)`. -/
theorem globalSectionsSpecMap_eq :
    globalSectionsSpecMap X = Spec.map (ofHom (algebraMap k (globalSectionsRing X))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

