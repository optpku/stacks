/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.Abelian
public import ReasLib.Topology.Sheaves.Stalks.Pullback
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TopCat

/- The canonical stalk-pullback owners are already isomorphisms in the coefficient category.
Specializing that category to `AddCommGrpCat` expresses exactly the source's assertion that the
underlying bijections respect the abelian-group structures, without introducing local wrappers. -/

universe u

/- Lemma 6.22.1 (1): for a continuous map `f : X ⟶ Y`, an abelian presheaf `𝒢` on `Y`, and a
point `x : X`, the canonical stalk identification is exactly the `AddCommGrpCat` specialization of
the owner `TopCat.Presheaf.stalkPullbackIso`. -/
namespace TopCat.Presheaf

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X)
variable (𝒢 : PAb(Y))

@[stacks 008O "inverse-image presheaf stalk bijection is an abelian-group isomorphism"]
#check
  (stalkPullbackIso AddCommGrpCat f 𝒢 x :
    𝒢.stalk (f x) ≅ ((pullback AddCommGrpCat f).obj 𝒢).stalk x)

end

end TopCat.Presheaf

/- Lemma 6.22.1 (2): for a continuous map `f : X ⟶ Y`, an abelian sheaf `𝒢` on `Y`, and a point
`x : X`, the canonical stalk identification is exactly the chapter bridge owner
`TopCat.Sheaf.stalkPullbackIso`. -/
namespace TopCat.Sheaf

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X)
variable (𝒢 : Ab(Y))

@[stacks 008O "inverse-image sheaf stalk bijection is an abelian-group isomorphism"]
#check
  (stalkPullbackIso f 𝒢 x :
    𝒢.presheaf.stalk (f x) ≅ ((f⁻¹).obj 𝒢).presheaf.stalk x)

end

end TopCat.Sheaf
