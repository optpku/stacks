/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Topos
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Topos
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Topos
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u w

variable (S : AlgebraicGeometry.Scheme.{u})
variable (τ : AlgebraicGeometry.StandardTopology)

/- Definition 59.21.1 (1): the small étale topos of a scheme is the category of
   sheaves of sets on its small étale site. -/
@[stacks 04HQ] #check
  (AlgebraicGeometry.Scheme.SmallEtaleTopos S :
    Type _)

/- Definition 59.21.1 (2): the small Zariski topos of a scheme is the category of
   sheaves of sets on its small Zariski site. -/
@[stacks 04HQ] #check
  (AlgebraicGeometry.Scheme.SmallZariskiTopos S :
    Type _)

/- Definition 59.21.1 (3): for each standard topology τ, the corresponding big
   topos is the category of sheaves of sets on the big τ site of S. -/
@[stacks 04HQ] #check
  (AlgebraicGeometry.StandardTopology.BigTopos τ S :
    Type _)
