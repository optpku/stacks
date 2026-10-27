/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing.Square

/-!
# Reverse kernel of a formal-glueing triple

Given modules `H` and `G` and an overlap morphism `φ`, the reverse module is the kernel of the
direct-sum comparison `j_* H ⊕ f_* G ⟶ (f ∘ j')_* (G|_V)` in `X.Modules`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing

/-- The `H`-leg of the reverse comparison: push `φ` forward along `f|_V` after the
pullback–pushforward unit, identify successive pushforwards with pushforward of the
composite, and rewrite the composite along the cartesian square. -/
def fromH {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (H : (U i).Modules) (G : Y.Modules)
    (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i)) :
    (pushforward (j i)).obj H ⟶
      (pushforward (j' f i ≫ f)).obj (restrict G (j' f i)) :=
  (pushforward (j i)).map
      ((pullbackPushforwardAdjunction (restrictF f i)).unit.app H ≫
        (pushforward (restrictF f i)).map φ) ≫
    (pushforwardComp (restrictF f i) (j i)).hom.app (restrict G (j' f i)) ≫
    eqToHom
      (congrArg (fun g : V f i ⟶ X ↦ (pushforward g).obj (restrict G (j' f i)))
        (square_comm f i))

/-- `fromH` is the unit-then-`φ` pushforward, transported along `pushforwardComp` and
the cartesian square. -/
theorem fromH_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (H : (U i).Modules) (G : Y.Modules)
    (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i)) :
    fromH f i H G φ =
      (pushforward (j i)).map
          ((pullbackPushforwardAdjunction (restrictF f i)).unit.app H ≫
            (pushforward (restrictF f i)).map φ) ≫
        (pushforwardComp (restrictF f i) (j i)).hom.app (restrict G (j' f i)) ≫
        eqToHom
          (congrArg (fun g : V f i ⟶ X ↦ (pushforward g).obj (restrict G (j' f i)))
            (square_comm f i)) :=
  sorry

/-- The `G`-leg of the reverse comparison: push the restriction unit of `j'` forward
along `f`, then identify successive pushforwards with `(f ∘ j')_*`. -/
def fromG {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (G : Y.Modules) :
    (pushforward f).obj G ⟶
      (pushforward (j' f i ≫ f)).obj (restrict G (j' f i)) :=
  (pushforward f).map ((restrictAdjunction (j' f i)).unit.app G) ≫
    (pushforwardComp (j' f i) f).hom.app (restrict G (j' f i))

/-- `fromG` is the restriction-unit pushforward, transported along `pushforwardComp`. -/
theorem fromG_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (G : Y.Modules) :
    fromG f i G =
      (pushforward f).map ((restrictAdjunction (j' f i)).unit.app G) ≫
        (pushforwardComp (j' f i) f).hom.app (restrict G (j' f i)) :=
  rfl

/-- The reverse comparison `j_* H ⊕ f_* G ⟶ (f ∘ j')_* (G|_V)`, as the copairing of
the `H`-leg and the negated `G`-leg. -/
def comparison {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (H : (U i).Modules) (G : Y.Modules)
    (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i)) :
    (pushforward (j i)).obj H ⊞ (pushforward f).obj G ⟶
      (pushforward (j' f i ≫ f)).obj (restrict G (j' f i)) :=
  biprod.desc (fromH f i H G φ) (-fromG f i G)

/-- `comparison` is the biproduct copairing of `fromH` and `-fromG`. -/
theorem comparison_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (H : (U i).Modules) (G : Y.Modules)
    (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i)) :
    comparison f i H G φ = biprod.desc (fromH f i H G φ) (-fromG f i G) :=
  rfl

/-- The reverse `𝒪_X`-module of a glueing triple `(H, G, φ)`, as the kernel of
`comparison`. -/
def reverse {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (H : (U i).Modules) (G : Y.Modules)
    (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i)) :
    X.Modules :=
  kernel (comparison f i H G φ)

namespace reverse

/-- The reverse kernel of a quasi-coherent glueing triple remains quasi-coherent
when `f` is quasi-compact and quasi-separated and `i` is of finite presentation. -/
instance instIsQuasicoherent {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    [QuasiCompact f] [QuasiSeparated f] [FinitePresentation i]
    (H : (U i).Modules) (G : Y.Modules)
    (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i))
    [H.IsQuasicoherent] [G.IsQuasicoherent] :
    (reverse f i H G φ).IsQuasicoherent :=
  sorry

end reverse

section

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
variable (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
variable {H H' : (U i).Modules} {G G' : Y.Modules}
variable (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i))
variable (φ' : (pullback (restrictF f i)).obj H' ⟶ restrict G' (j' f i))
variable (a : H ⟶ H') (b : G ⟶ G')
variable (w : (pullback (restrictF f i)).map a ≫ φ' =
  φ ≫ (restrictFunctor (j' f i)).map b)

include w in
/-- Compatible component maps carry the reverse kernel into the target reverse kernel. -/
private theorem reverseMap_condition :
    (kernel.ι (comparison f i H G φ) ≫
      biprod.map ((pushforward (j i)).map a) ((pushforward f).map b)) ≫
        comparison f i H' G' φ' = 0 :=
  sorry

/-- Compatible morphisms of the two components induce a morphism of reverse kernels. -/
@[no_expose] def reverseMap : reverse f i H G φ ⟶ reverse f i H' G' φ' :=
  kernel.lift (comparison f i H' G' φ')
    (kernel.ι (comparison f i H G φ) ≫
      biprod.map ((pushforward (j i)).map a) ((pushforward f).map b))
    (reverseMap_condition f i φ φ' a b w)

/-- The induced reverse-kernel morphism restricts the biproduct of the pushforward maps. -/
theorem reverseMap_ι :
    reverseMap f i φ φ' a b w ≫ kernel.ι (comparison f i H' G' φ') =
      kernel.ι (comparison f i H G φ) ≫
        biprod.map ((pushforward (j i)).map a) ((pushforward f).map b) := by
  exact kernel.lift_ι _ _ _

end

end AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing
