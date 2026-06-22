import Mathlib

set_option quotPrecheck false
--Ch 2. HILBERT'S AXIOMS
--INTRO:
--Hartshorne presents Hilbert's axioms in higher order logic.
--`Point` is a primitive ``sort (or type)``.
--`Line : (Point→Prop)→Prop` is a primitive relation.
-- `Line` is a ``2nd-order relation of 1-arity``.
--`L∈Line` abbreviates the propositions `Line L`.
--`L∈Line` reads `L is a line`; lines are thought of as sets of points.
--Lean has built in support for higher order logic via `Set`.
--`Set Point` is syntactic sugar for `Point→Prop`.
--`L: Set Point` means `L : Point→Prop` is a ``1st-order property``.
--Any set can be thought of as the extension of a property.
#print Set
--Sets have basic constructive principles supporting them in Lean.
open Set
--One is the usual axiom of extensionality.
example {T:Type} (S₁ S₂:Set T) : (∀x:T, x∈S₁ ↔ x∈S₂) → S₁=S₂ := ext
--`∀L∈Line, P L` abbreviates `∀L:Set Point, Line L → P L`.
--By definition, the comprehension axiom comes for free.
--I.e. for any property `P:Point→Prop`, there is a set `{p:Point ∣ P p}`.

--Sec 6. AXIOMS OF INCIDENCE
--A set of points `Point` and collection of subsets of points `Line`,
-- is an `Incidence_Geometery` iff the following axioms are satsified.
class Incidence_Geometery (Point : Type) (Line : Set (Set Point)) where
  I1 : ∀p₁ p₂:Point, p₁≠p₂ → ∃!L, Line L ∧ p₁∈L ∧ p₂∈L
  I2 : ∀L, Line L → ∃p₁ p₂:Point, p₁≠p₂ ∧ p₁∈L ∧ p₂∈L
  I3 : let Colinear (p₁ p₂ p₃:Point) : Prop := ∃!L, Line L ∧ p₁∈L ∧ p₂∈L ∧ p₃∈L
    ∃p₁ p₂ p₃:Point, ¬ Colinear p₁ p₂ p₃

--Originally this development postulated `Point`, `Line`, `Between` and the
--Hilbert axioms `I1`-`I3`, `B1`-`B4` as global Lean `axiom`s. We instead
--bundle all of the primitive notions and axioms into a single typeclass
--`HilbertGeo`. This keeps every result below stated and proved for an
--*arbitrary* incidence-betweenness geometry (rather than relying on global
--axioms), which is exactly the class of results Hartshorne is after, and it
--avoids introducing unproven global `axiom`s into the project.
class HilbertGeo (Point : Type) where
  --(primitive) `IsLine L` reads `L is a line`.
  IsLine : Set (Set Point)
  --(primitive) `Btw A B C` reads `B is between A and C`, i.e. `A⋆B⋆C`.
  Btw : Point → Point → Point → Prop
  --(I1) Every pair of distint points is contained in a unique Line.
  I1 : ∀p₁ p₂:Point, p₁≠p₂ → ∃!L, IsLine L ∧ p₁∈L ∧ p₂∈L
  --(I2) Every line contains two distinct points.
  I2 : ∀L, IsLine L → ∃p₁ p₂:Point, p₁≠p₂ ∧ p₁∈L ∧ p₂∈L
  --(I3) There exists three noncolinear points.
  I3 : ∃p₁ p₂ p₃:Point, ¬ ∃L, IsLine L ∧ p₁∈L ∧ p₂∈L ∧ p₃∈L
  --(B1) If `A⋆B⋆C` then `A,B,C` are distinct points which
  -- lie on the same line and `C⋆B⋆A`.
  B1 : ∀A B C:Point, Btw A B C → A≠B ∧ A≠C ∧ B≠C ∧
    Btw C B A ∧ ∃l:Set Point, IsLine l ∧ A∈l ∧ B∈l ∧ C∈l
  --(B2) For distinct points `A,B`, there exists point `C`
  -- such that `A⋆B⋆C`.
  B2 : ∀A B:Point, A≠B → ∃C:Point, Btw A B C
  --(B3) Given three distinct points on a line, one and only one of them
  -- is between the other two.
  B3 : ∀A B C:Point, ∀l, IsLine l → A≠B ∧ A≠C ∧ B≠C ∧ A∈l ∧ B∈l ∧ C∈l →
     (Btw A B C  ∧ ¬Btw C A B ∧ ¬Btw B C A) ∨
     (¬Btw A B C  ∧ Btw C A B ∧ ¬Btw B C A) ∨
     (¬Btw A B C  ∧ ¬Btw C A B ∧ Btw B C A)
  --(B4) Pasch's axiom. Let `A,B,C` be noncolinear points, none of which
  -- are contained in a line `l`. If `l` contains a point `D` lying between
  -- `A,C` (i.e. `l` crosses side `AC`), then it must contain a point lying
  -- between `A,B` or between `B,C`, but not both (i.e. `l` crosses exactly
  -- one of the two remaining sides `AB`, `BC`).
  --
  -- CORRECTION: the original formulation of `B4` referred to side `AC`
  -- (`Btw A D₁ C`) in the *conclusion* as well as in the hypothesis, which
  -- makes it false in the Euclidean plane (a line crossing `AC` may also
  -- cross `BC`). The conclusion's first segment is meant to be side `AB`
  -- (`Btw A D₁ B`); this is the standard Pasch axiom, which we use here.
  B4 : ∀(A B C:Point) (l: Set Point), IsLine l →
    (¬∃L, IsLine L ∧ A∈L ∧ B∈L ∧ C∈L) → A∉l → B∉l → C∉l →
    (∃D:Point, D∈l ∧ Btw A D C) →
    ((∃D₁:Point, D₁∈l ∧ Btw A D₁ B) ∧ (¬∃D₂:Point, D₂∈l ∧ Btw B D₂ C)) ∨
    ((¬∃D₁:Point, D₁∈l ∧ Btw A D₁ B) ∧ (∃D₂:Point, D₂∈l ∧ Btw B D₂ C))

namespace HilbertGeo

variable {Point : Type} [HilbertGeo Point]

--`Line` and `Between` are convenient names for the primitive notions of
--the ambient geometry, recovering Hartshorne's surface syntax.
abbrev Line : Set (Set Point) := IsLine
abbrev Between (A B C : Point) : Prop := Btw A B C

--(def) Three points are `Colinear` iff they all lie on the same line.
--`Colinear` is a ``1st-order property of 3-artiy``.
abbrev Colinear (p₁ p₂ p₃:Point) : Prop := ∃L, Line L ∧ p₁∈L ∧ p₂∈L ∧ p₃∈L

--(6.1) Two distinct lines intersect at most on one point.
lemma Prop6_1 : ∀ᵉ(L₁∈(Line : Set (Set Point)))(L₂∈(Line : Set (Set Point))), L₁≠L₂ →
  ¬∃p₁ p₂:Point, p₁∈L₁ ∧ p₂∈L₁ ∧ p₁∈L₂ ∧ p₂∈L₂ ∧ p₁≠p₂ := by
  rintro L₁ hL₁ L₂ hL₂ hL ⟨p₁, p₂, h11, h12, h21, h22, hp⟩
  obtain ⟨L, ⟨_, _⟩, h⟩ := I1 p₁ p₂ hp; dsimp at h
  apply hL
  have := h L₁ ⟨hL₁, h11, h12⟩
  have := h L₂ ⟨by assumption, by assumption, by assumption⟩
  rw[this]; assumption

--(def) Parralell lines have either no points or all points in common.
--`Parallel` is a ``2nd-order property of 2-arity`.
def Parallel (L₁ L₂: Set Point): Prop
  := Line L₁ ∧ Line L₂ ∧ (L₁=L₂ ∨ ¬∃p:Point, p∈L₁ ∧ p∈L₂)
--(P) For each point `p` and line `L` there is at most one line
-- containing `p` parralell to `L`.
--Parallel axiom `P` that may or may not be used, and is thus defined.
--`P` is a ``0th-order property``, i.e. a proposition.
def P : Prop :=  ∀ᵉ(p:Point) (L∈(Line : Set (Set Point))), ¬∃L₁ L₂,
  p∈L₁ ∧ p∈L₂ ∧ Parallel L L₁ ∧ Parallel L L₂ ∧ L₁≠L₂

/-
Sec 6. Sud's Exercises (useful for future sections!)

Here are alternative axiomatizations of `I2` and `I3`.
The purpose is to make future proofs constructive.

For every line, there exists three distinct points:
two lie on the line, and one does not.
Hint: suppose false; try to contraict `I3`.
Note: this cannot be proven constructively from the axioms!
This is why I tihnk this is a better axiom!
-/
lemma SudI2 (l: Set Point) (_ :Line l) : ∃p₁ p₂ p₃:Point,
   p₃∉l ∧ p₂∈l ∧ p₁∈l ∧ p₁≠p₂ ∧ p₁≠p₃ ∧ p₂≠p₃ := by
  --Take any line `l`. There are two disctinct points already on the line.
  --So we must find a third not on the line.
  --Commands ``by_contra h`` and ``push_neg at h`` are useful.
  rename_i h;
  obtain ⟨ p₁, p₂, hp₁p₂ ⟩ := ‹HilbertGeo Point›.I2 l h;
  obtain ⟨ p₃, hp₃ ⟩ := ‹HilbertGeo Point›.I3;
  by_cases hp₃l : p₃ ∈ l;
  · grind;
  · exact ⟨ p₁, p₂, p₃, hp₃l, hp₁p₂.2.2, hp₁p₂.2.1, hp₁p₂.1, by aesop ⟩

--There exists a line.
--NOTE: As stated this does *not* follow from the Hilbert axioms above: the
--one-point geometry with no lines (`Point` a singleton, `IsLine = ∅`,
--`Btw` always false) satisfies `I1`-`I3` and `B1`-`B4` vacuously, yet has
--no line, since `I3` is witnessed by the degenerate triple `(p,p,p)`.
--Hence this lemma is left as `sorry`; it is unprovable from the axioms.
lemma SudI3 : ∃l:Set Point, (Line : Set (Set Point)) l := by
  sorry


--Sec 7. Axioms of Betweenness
--`Between A B C` means `B` is between `A` and `C`.

--(def) If `A,B` are distinct points then `Seg A B` is the set consisting
-- of points `A,B` and all those inbetween `A,B`.
--We define `Seg` on all points for simplicity; any result using seg will
-- usually have distinctness inferable from context.
--`Seg` is a ``2nd-order function of 2-arity`.
def Seg (A B :Point) : Set Point :=
  { P | (fun X ↦ X=A ∨ X=B ∨ Between B X A) P }
--(def) If `A,B,C` are noncolinear points, then `Tri A B C` is the union
-- of segements `A↑B, A↑C, B↑C`. Think of `Tri A B C` as the boundary
-- of a 2-simplex. Again we define `Tri` on all points and expect
-- any context involving triangles to prove noncolinearity.
--`ΔABC` denotes `Tri A B C`.
--`Tri` is a ``2nd-order function of 3-arity``.
def Tri (A B C:Point) : Set Point :=
  Seg A B ∪ Seg A C ∪ Seg B C
notation:85 "Δ" A:85 B:85 C:85 => Tri A B C
--Note: Segements `Seg A B` and `Seg B A` are equal.
lemma Note7_1 (A B:Point) : Seg A B = Seg B A := by
  unfold Seg; apply ext; intro x
  constructor
  repeat intro h; simp only [mem_setOf]; obtain (_ |_ | h3) := h;
  · right; left; assumption
  · left; assumption
  · right; right
    obtain ⟨ _, _, _ ,mark, _⟩  := B1 B x A h3
    exact mark
  · simp; rintro (_ | _ | h3);
    · right; left; assumption
    · left; assumption
    · right; right
      obtain ⟨ _, _, _ ,mark, _⟩  := B1 A x B h3
      exact mark

--Sec 7. Plane separation infrastructure.
--We say two points are on the `SameSide` of a line `l` when the segment
--joining them does not meet `l`. For points off `l`, the negation of
--`SameSide` is "lie on opposite sides of `l`". With this single relation the
--two "sides" of `l` are the two classes of points off `l`.

/-- `SameSide l A B` holds when the segment `A↑B` does not meet the line `l`. -/
def SameSide (l : Set Point) (A B : Point) : Prop := Seg A B ∩ l = ∅

--Membership in a segment, unfolded.
lemma mem_Seg {A B x : Point} : x ∈ Seg A B ↔ x = A ∨ x = B ∨ Between B x A := Iff.rfl

/-
A degenerate segment is a single point.
-/
lemma Seg_self (A : Point) : Seg A A = {A} := by
  -- Since $A$ is in the segment $Seg A A$, we need to show that $A$ is the only point in this segment.
  ext x
  simp [Seg];
  grind +suggestions

/-
`SameSide` is reflexive on points off `l`.
-/
lemma SameSide_refl {l : Set Point} {A : Point} (hA : A ∉ l) : SameSide l A A := by
  unfold SameSide; simp [Seg_self, hA]

/-
`SameSide` is symmetric.
-/
lemma SameSide_symm {l : Set Point} {A B : Point} (h : SameSide l A B) : SameSide l B A := by
  unfold SameSide at *;
  simp_all +decide [ Note7_1 ]

/-
For endpoints off `l`, a segment meets `l` exactly at an interior point.
-/
lemma not_SameSide_iff {l : Set Point} {A B : Point} (hA : A ∉ l) (hB : B ∉ l) :
    ¬ SameSide l A B ↔ ∃ D, D ∈ l ∧ Between B D A := by
      constructor <;> intro h;
      · grind +locals;
      · obtain ⟨ D, hD₁, hD₂ ⟩ := h; intro T; have := T.symm; simp_all +decide [ Set.ext_iff ] ;
        exact this D ( by unfold Seg; tauto ) hD₁

/-
A point on the opposite side of `A` exists (the other side is nonempty).
Take a point `P₁ ∈ l` (from `I2`) and extend `A,P₁` past `P₁` by `B2`.
-/
lemma exists_opp {l : Set Point} (hl : Line l) {A : Point} (hA : A ∉ l) :
    ∃ C, C ∉ l ∧ ¬ SameSide l A C := by
      rename_i h;
      obtain ⟨ P₁, P₂, hP₁P₂, hP₁, hP₂ ⟩ := h.I2 l hl;
      obtain ⟨ C, hC ⟩ := h.B2 A P₁ ( by aesop );
      refine' ⟨ C, _, _ ⟩;
      · intro hC';
        have := h.B1 A P₁ C hC;
        obtain ⟨ l', hl', hA', hP₁', hC' ⟩ := this.2.2.2.2; have := h.I1 P₁ C; simp_all +decide [ ExistsUnique ] ;
        grind;
      · refine' Set.Nonempty.ne_empty _;
        use P₁;
        have := h.B1 _ _ _ hC;
        exact ⟨ by unfold Seg; aesop, hP₁ ⟩

--Betweenness order theory (Hilbert/Hartshorne §7), needed for the collinear
--cases of plane separation. These are 1-dimensional facts about the linear
--order induced by betweenness on a line; their proofs use Pasch (`B4`) via an
--auxiliary point off the line.

--Interpolation: if `D` is strictly between `A` and `C`, and `B` is any other
--point collinear with them, then `D` is between `A` and `B`, or between `B`
--and `C`. (`D` lies in segment `AB` or segment `BC`.)
lemma betw_interpolate {A B C D : Point} (hcol : Colinear A B C)
    (hADC : Btw A D C) (hBA : B ≠ A) (hBC : B ≠ C) (hBD : B ≠ D) :
    Btw A D B ∨ Btw B D C := by sorry

--A single point `D` cannot be strictly between `A` and `B`, between `B` and
--`C`, and between `A` and `C` simultaneously: if `D` is between `A,B` and
--between `B,C` then `A` and `C` lie on the same side of `D`, so `D` is not
--between `A` and `C`.
lemma betw_not_all {A B C D : Point}
    (h1 : Btw A D B) (h2 : Btw B D C) : ¬ Btw A D C := by sorry

/-
KEY (transitivity): `SameSide` is transitive on points off `l`.
This is the heart of plane separation. For a noncollinear triple `A B C`
it is Pasch's axiom `B4`; for a collinear triple it uses `B3`, `Prop6_1`
and `betw_interpolate`.
-/
lemma SameSide_trans {l : Set Point} {A B C : Point} (hl : Line l)
    (hA : A ∉ l) (hB : B ∉ l) (hC : C ∉ l)
    (hAB : SameSide l A B) (hBC : SameSide l B C) : SameSide l A C := by
      revert hAB hBC;
      by_contra! h_contra;
      obtain ⟨D, hDl, hADC⟩ : ∃ D, D ∈ l ∧ ‹HilbertGeo Point›.Btw A D C := by
        simp_all +decide [ SameSide ];
        simp_all +decide [ Set.ext_iff, Seg ];
        obtain ⟨ D, hD₁, hD₂ ⟩ := h_contra.2.2; use D; have := ‹HilbertGeo Point›.B1 _ _ _ hD₁; aesop;
      by_cases hBtw : ‹HilbertGeo Point›.Btw A D B ∨ ‹HilbertGeo Point›.Btw B D C;
      · cases hBtw <;> have := ‹HilbertGeo Point›.B1 _ _ _ ‹_› <;> simp_all +decide [ SameSide ]; all_goals simp_all +decide [ Set.ext_iff, Seg ];
      · by_cases hcol : ‹HilbertGeo Point›.Colinear A B C;
        · have := ‹HilbertGeo Point›.betw_interpolate hcol hADC (by
          grind +splitIndPred) (by
          rintro rfl; simp_all +decide [ SameSide ]) (by
          grind);
          contradiction;
        · have := ‹HilbertGeo Point›.B4 A B C l hl hcol hA hB hC ⟨ D, hDl, hADC ⟩ ; simp_all +decide [ SameSide ] ;
          cases this <;> simp_all +decide [ Set.ext_iff ];
          · rename_i h; obtain ⟨ ⟨ D₁, hD₁l, hD₁ ⟩, hD₂ ⟩ := h; exact h_contra.1 D₁ ( by
              exact Or.inr <| Or.inr <| by simpa [ Btw ] using ‹HilbertGeo Point›.B1 _ _ _ hD₁ |>.2.2.2.1; ) hD₁l;
          · rename_i h; obtain ⟨ D₂, hD₂l, hBtw₂ ⟩ := h.2; simp_all +decide [ Seg ] ;
            exact h_contra.2.1.2.2 D₂ ( by have := ‹HilbertGeo Point›.B1 _ _ _ hBtw₂; tauto ) hD₂l

/-
KEY (at most two sides): `l` cannot put all three pairs on opposite sides.
For noncollinear `A B C` this is the "not both" half of Pasch `B4`; for a
collinear triple it uses `B3` and `Prop6_1` (a line meets a line once).
-/
lemma not_all_opp {l : Set Point} {A B C : Point} (hl : Line l)
    (hA : A ∉ l) (hB : B ∉ l) (hC : C ∉ l) :
    ¬ (¬ SameSide l A B ∧ ¬ SameSide l B C ∧ ¬ SameSide l A C) := by
      intro h;
      have hD₁ : ∃ D₁ ∈ l, (‹HilbertGeo Point›.Btw B D₁ C) := by
        have := @not_SameSide_iff Point ‹_› l B C;
        exact this hB hC |>.1 h.2.1 |> fun ⟨ D, hD₁, hD₂ ⟩ => ⟨ D, hD₁, by have := ‹HilbertGeo Point›.B1 _ _ _ hD₂; tauto ⟩
      obtain ⟨D₁, hD₁⟩ := hD₁
      have hD₂ : ∃ D₂ ∈ l, (‹HilbertGeo Point›.Btw A D₂ C) := by
        have := @not_SameSide_iff Point ‹HilbertGeo Point› l A C hA hC;
        exact this.mp h.2.2 |> fun ⟨ D₂, hD₂₁, hD₂₂ ⟩ => ⟨ D₂, hD₂₁, by have := ‹HilbertGeo Point›.B1 _ _ _ hD₂₂; tauto ⟩
      obtain ⟨D₂, hD₂⟩ := hD₂
      have hD₃ : ∃ D₃ ∈ l, (‹HilbertGeo Point›.Btw A D₃ B) := by
        rename_i h_geo;
        have := h.1; unfold SameSide at this; simp_all +decide [ Set.ext_iff ] ;
        obtain ⟨ x, hx₁, hx₂ ⟩ := this; use x; simp_all +decide [ Seg ] ;
        rcases hx₁ with ( rfl | rfl | hx₁ ) <;> simp_all +decide [ Between ];
        exact h_geo.B1 _ _ _ hx₁ |>.2.2.2.1
      obtain ⟨D₃, hD₃⟩ := hD₃;
      by_cases hCollinear : ‹HilbertGeo Point›.Colinear A B C;
      · -- Since A, B, C are collinear, by B1, the line through A and B is the same as the line through B and C, and the line through A and C.
        obtain ⟨m, hm⟩ : ∃ m : Set Point, (‹HilbertGeo Point›.IsLine m) ∧ A ∈ m ∧ B ∈ m ∧ C ∈ m := by
          exact hCollinear;
        -- Since $D₁$, $D₂$, and $D₃$ are all on $m$, and $m$ is a line, they must all be the same point.
        have hD_eq : D₁ = D₂ ∧ D₂ = D₃ := by
          have hD_eq : D₁ ∈ m ∧ D₂ ∈ m ∧ D₃ ∈ m := by
            have := ‹HilbertGeo Point›.B1 B D₁ C; have := ‹HilbertGeo Point›.B1 A D₂ C; have := ‹HilbertGeo Point›.B1 A D₃ B; simp_all +decide ;
            have := ‹HilbertGeo Point›.I1 B C; have := ‹HilbertGeo Point›.I1 A C; have := ‹HilbertGeo Point›.I1 A B; simp_all +decide [ ExistsUnique ] ;
            grind;
          have hD_eq : ∀ p q : Point, p ∈ m → q ∈ m → p ∈ l → q ∈ l → p = q := by
            intros p q hp hq hp_l hq_l
            by_cases h_eq : p = q;
            · exact h_eq;
            · have := ‹HilbertGeo Point›.Prop6_1;
              exact Classical.not_not.1 fun h => this m hm.1 l hl ( by aesop ) ⟨ p, q, hp, hq, hp_l, hq_l, h ⟩;
          exact ⟨ hD_eq _ _ ( by tauto ) ( by tauto ) ( by tauto ) ( by tauto ), hD_eq _ _ ( by tauto ) ( by tauto ) ( by tauto ) ( by tauto ) ⟩;
        have := ‹HilbertGeo Point›.betw_not_all hD₃.2 ( by aesop ) ; aesop;
      · have := ‹HilbertGeo Point›.B4 A B C l hl hCollinear hA hB hC ⟨ D₂, hD₂.1, hD₂.2 ⟩ ; simp_all +decide [ SameSide ] ;
        grind

/-
Derived: two points each opposite to `A` lie on the same side as each other.
-/
lemma opp_opp_same {l : Set Point} {A B C : Point} (hl : Line l)
    (hA : A ∉ l) (hB : B ∉ l) (hC : C ∉ l)
    (hAB : ¬ SameSide l A B) (hAC : ¬ SameSide l A C) : SameSide l B C := by
      exact Classical.not_not.1 fun h => by have := ‹HilbertGeo Point›.not_all_opp hl hA hB hC; tauto;

/-
Two points off `l` lie on the same side relative to a reference point `A₀`
(both same-side as `A₀`, or both opposite to `A₀`) iff they are on the same
side of `l` as each other.
-/
lemma sameClass {l : Set Point} {A₀ A B : Point} (hl : Line l)
    (h0 : A₀ ∉ l) (hA : A ∉ l) (hB : B ∉ l) :
    ((SameSide l A₀ A ∧ SameSide l A₀ B) ∨ (¬ SameSide l A₀ A ∧ ¬ SameSide l A₀ B))
      ↔ SameSide l A B := by
        by_contra h_contra;
        push_neg at h_contra;
        cases' h_contra with h h;
        · cases h.1 <;> simp_all +decide [ SameSide_symm ];
          · rename_i h';
            exact h ( ‹HilbertGeo Point›.SameSide_trans hl hA h0 hB ( ‹HilbertGeo Point›.SameSide_symm h'.1 ) h'.2 );
          · grind +suggestions;
        · cases h.1.1 ( by
            apply Classical.byContradiction
            intro h_contra;
            have := @HilbertGeo.SameSide_trans Point ‹_› l A₀ B A hl h0 hB hA; simp_all +decide [ SameSide_symm ] ; ) ( by
            grind +suggestions )

/-
Two points off `l` lie in opposite classes relative to `A₀` iff they are on
opposite sides of `l` from each other.
-/
lemma diffClass {l : Set Point} {A₀ A B : Point} (hl : Line l)
    (h0 : A₀ ∉ l) (hA : A ∉ l) (hB : B ∉ l) :
    ((SameSide l A₀ A ∧ ¬ SameSide l A₀ B) ∨ (¬ SameSide l A₀ A ∧ SameSide l A₀ B))
      ↔ ¬ SameSide l A B := by
        have := @sameClass Point ‹_› l A₀ A B hl h0 hA hB; tauto;

--(7.1) Plane separation. Let `l` be a line.
--The set of points not lying on `l` can be partitioned into two nonempty
--subsets `S₁` and `S₂` satisfying the following properties:
--(a) Points `A, B` not in `l`, belong to the same set (`S₁` or `S₂`) iff
--`Seg A B` does not intersect `l`, and
--(b) Points `A, C` not in `l` belong to the opposite sets (one in `S₁`,
--other in `S₂`) iff `Seg A C` intersects `l`.


lemma Prop7_1 (l:Set Point) (hl : Line l) : ∃ S₁ S₂ : Set Point,
  (∃x, x∈S₁) ∧ (∃x, x∈S₂) ∧ S₁∩S₂=∅ ∧ S₁∪S₂ = univ \ l ∧
  (∀ A B:Point, A∉l → B∉l →
    ((A∈S₁ ∧ B∈S₁) ∨ (A∈S₂ ∧ B∈S₂) ↔ Seg A B ∩ l = ∅))
  ∧
  (∀ A B :Point, A∉l → B∉l →
    ((A∈S₁ ∧ B∈S₂) ∨ (A∈S₂ ∧ B∈S₁) ↔ ∃x, x∈ Seg A B ∧ x∈l)) := by
  obtain ⟨_, _, A₀, hA₀, _, _, _, _, _⟩ := SudI2 l hl
  refine ⟨{P | P ∉ l ∧ SameSide l A₀ P}, {P | P ∉ l ∧ ¬ SameSide l A₀ P},
    ⟨A₀, hA₀, SameSide_refl hA₀⟩, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨C, hCl, hCopp⟩ := exists_opp hl hA₀
    exact ⟨C, hCl, hCopp⟩
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro P ⟨⟨_, h1⟩, _, h2⟩
    exact h2 h1
  · ext P
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_diff, Set.mem_univ, true_and]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hP
      by_cases h : SameSide l A₀ P
      · exact Or.inl ⟨hP, h⟩
      · exact Or.inr ⟨hP, h⟩
  · intro A B hA hB
    simp only [Set.mem_setOf_eq, hA, hB, not_false_eq_true, true_and]
    exact sameClass hl hA₀ hA hB
  · intro A B hA hB
    simp only [Set.mem_setOf_eq, hA, hB, not_false_eq_true, true_and]
    rw [diffClass hl hA₀ hA hB]
    show Seg A B ∩ l ≠ ∅ ↔ _
    rw [← Set.nonempty_iff_ne_empty, Set.inter_nonempty]

end HilbertGeo