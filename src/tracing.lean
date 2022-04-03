import data.nat.gcd
import data.real.irrational

lemma even_of_even_sqr {m : ℕ} (h : 2 ∣ m^2) : 2 ∣ m :=
begin
  rw [pow_two, nat.prime_two.dvd_mul] at h,
  cases h; assumption
end

-- So here's one path down: 

theorem pow_two (a : M) : a^2 = a * a :=
by rw [pow_succ, pow_one]

theorem pow_one (a : M) : a^1 = a :=
by rw [pow_succ, pow_zero, mul_one]

theorem pow_succ (a : M) (n : ℕ) : a^(n+1) = a * a^n := monoid.npow_succ' n a

class monoid (M : Type u) extends semigroup M, mul_one_class M :=
(npow : ℕ → M → M := npow_rec)
(npow_zero' : ∀ x, npow 0 x = 1 . try_refl_tac)
(npow_succ' : ∀ (n : ℕ) x, npow n.succ x = x * npow n x . try_refl_tac)

def npow_rec [has_one M] [has_mul M] : ℕ → M → M
| 0     a := 1
| (n+1) a := a * npow_rec n a


-- Yeah, probably worth looking at a few paths down and seeing what feels good. 
-- This one is ok, not great. 
-- well, idk, maybe it does kinda make sense? I think with sme focuse I could make sense 
-- of the pow two path. 
-- what's down the nat.prime_two.dvd_mul path?
-- having to hack around here a bit: 
-- https://leanprover-community.github.io/mathlib_docs/data/nat/prime.html#nat.prime.dvd_mul
-- https://github.com/leanprover-community/mathlib/blob/12128187f1905ff2a5a2de1d60d788728822c9d1/src/data/nat/prime.lean#L554
-- Ok, yeah it's the version of this when p is two

theorem prime.dvd_mul {p m n : ℕ} (pp : prime p) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n :=
⟨λ H, or_iff_not_imp_left.2 $ λ h,
  (pp.coprime_iff_not_dvd.2 h).dvd_of_dvd_mul_left H,
 or.rec (λ h : p ∣ m, h.mul_right _) (λ h : p ∣ n, h.mul_left _)⟩

 theorem or_iff_not_imp_left : a ∨ b ↔ (¬ a → b) := decidable.or_iff_not_imp_left

protected theorem decidable.or_iff_not_imp_left [decidable a] : a ∨ b ↔ (¬ a → b) :=
⟨or.resolve_left, λ h, dite _ or.inl (or.inr ∘ h)⟩

theorem coprime.dvd_of_dvd_mul_left {m n k : ℕ} (H1 : coprime k m) (H2 : k ∣ m * n) : k ∣ n :=
by rw mul_comm at H2; exact H1.dvd_of_dvd_mul_right H2

theorem prime.coprime_iff_not_dvd {p n : ℕ} (pp : prime p) : coprime p n ↔ ¬ p ∣ n :=
⟨λ co d, pp.not_dvd_one $ co.dvd_of_dvd_mul_left (by simp [d]),
 λ nd, coprime_of_dvd $ λ m m2 mp, ((prime_dvd_prime_iff_eq m2 pp).1 mp).symm ▸ nd⟩

theorem dvd_gcd {m n k : ℕ} : k ∣ m → k ∣ n → k ∣ gcd m n :=
gcd.induction m n (λn _ kn, by rw gcd_zero_left; exact kn)
  (λn m mpos IH H1 H2, by rw gcd_rec; exact IH ((dvd_mod_iff H1).2 H2) H1)

@[simp] theorem gcd_zero_left (x : nat) : gcd 0 x = x := by simp [gcd]

def gcd : nat → nat → nat
| 0        y := y
| (succ x) y := have y % succ x < succ x, from mod_lt _ $ succ_pos _,
                gcd (y % succ x) (succ x)

---in core.lean
inductive nat
| zero : nat
| succ (n : nat) : nat

lemma mod_lt (x : nat) {y : nat} (h : 0 < y) : x % y < y :=
begin
  induction x using nat.case_strong_induction_on with x ih,
  { rw zero_mod, assumption },
  { by_cases h₁ : succ x < y,
    { rwa [mod_eq_of_lt h₁] },
    { have h₁ : succ x % y = (succ x - y) % y := mod_eq_sub_mod (not_lt.1 h₁),
      have : succ x - y ≤ x := le_of_lt_succ (nat.sub_lt (succ_pos x) h),
      have h₂ : (succ x - y) % y < y := ih _ this,
      rwa [← h₁] at h₂ } }
end

@[simp] lemma zero_mod (b : nat) : 0 % b = 0 :=
begin
  rw mod_def,
  have h : ¬(0 < b ∧ b ≤ 0),
  {intro hn, cases hn with l r, exact absurd (lt_of_lt_of_le l r) (lt_irrefl 0)},
  simp [if_neg, h]
end

@[trans] lemma lt_of_lt_of_le : ∀ {a b c : α}, a < b → b ≤ c → a < c
| a b c hab hbc :=
  let ⟨hab, hba⟩ := le_not_le_of_lt hab in
  lt_of_le_not_le (le_trans hab hbc) $ λ hca, hba (le_trans hbc hca)

lemma le_not_le_of_lt : ∀ {a b : α}, a < b → a ≤ b ∧ ¬ b ≤ a
| a b hab := lt_iff_le_not_le.mp hab

lemma lt_iff_le_not_le : ∀ {a b : α}, a < b ↔ (a ≤ b ∧ ¬ b ≤ a) :=
preorder.lt_iff_le_not_le


class preorder (α : Type u) extends has_le α, has_lt α :=
(le_refl : ∀ a : α, a ≤ a)
(le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
(lt := λ a b, a ≤ b ∧ ¬ b ≤ a)
(lt_iff_le_not_le : ∀ a b : α, a < b ↔ (a ≤ b ∧ ¬ b ≤ a) . order_laws_tac)

-- back to core
class has_le       (α : Type u) := (le : α → α → Prop)
class has_lt       (α : Type u) := (lt : α → α → Prop)


theorem coprime.dvd_of_dvd_mul_right {m n k : ℕ} (H1 : coprime k n) (H2 : k ∣ m * n) : k ∣ m :=
let t := dvd_gcd (dvd_mul_left k m) H2 in
by rwa [gcd_mul_left, H1.gcd_eq_one, mul_one] at t

theorem prime.not_dvd_one {p : ℕ} (pp : prime p) : ¬ p ∣ 1
| d := (not_le_of_gt pp.one_lt) $ le_of_dvd dec_trivial d

lemma not_le_of_gt {a b : α} (h : a > b) : ¬ a ≤ b :=
(le_not_le_of_lt h).right

lemma le_not_le_of_lt : ∀ {a b : α}, a < b → a ≤ b ∧ ¬ b ≤ a
| a b hab := lt_iff_le_not_le.mp hab

lemma lt_iff_le_not_le : ∀ {a b : α}, a < b ↔ (a ≤ b ∧ ¬ b ≤ a) :=
preorder.lt_iff_le_not_le

class preorder (α : Type u) extends has_le α, has_lt α :=
(le_refl : ∀ a : α, a ≤ a)
(le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
(lt := λ a b, a ≤ b ∧ ¬ b ≤ a)
(lt_iff_le_not_le : ∀ a b : α, a < b ↔ (a ≤ b ∧ ¬ b ≤ a) . order_laws_tac)

--These are in core.lean!
class has_le       (α : Type u) := (le : α → α → Prop)
class has_lt       (α : Type u) := (lt : α → α → Prop)

--Hmmm, this is getting pretty intersting! 
--I think we could understand this path down, buuuut
-- let me look at a couple others right quick
-- I feel like the path through the ring would be farily complicated?
-- Let me poke at it for 1 min

have : 2 * (2 * k^2) = 2 * n^2,
{ rw [←sqr_eq, meq], ring },

meta def ring (red : parse (tk "!")?) : tactic unit :=
ring1 red <|>
(ring_nf red normalize_mode.horner (loc.ns [none]) >> trace "Try this: ring_nf")


--hmmm yeah ring is like real general, wich makes sense...#check
/-- If `ring` fails to close the goal, it falls back on normalizing the expression to a "pretty"
form so that you can see why it failed. This setting adjusts the resulting form:

  * `raw` is the form that `ring` actually uses internally, with iterated applications of `horner`.
    Not very readable but useful if you don't want any postprocessing.
    This results in terms like `horner (horner (horner 3 y 1 0) x 2 1) x 1 (horner 1 y 1 0)`.
  * `horner` maintains the Horner form structure, but it unfolds the `horner` definition itself,
    and tries to otherwise minimize parentheses.
    This results in terms like `(3 * x ^ 2 * y + 1) * x + y`.
  * `SOP` means sum of products form, expanding everything to monomials.
    This results in terms like `3 * x ^ 3 * y + x + y`. -/
@[derive [has_reflect, decidable_eq]]
inductive normalize_mode | raw | SOP | horner

instance : inhabited normalize_mode := ⟨normalize_mode.horner⟩

/-- A `ring`-based normalization simplifier that rewrites ring expressions into the specified mode.
  See `normalize`. This version takes a list of atoms to persist across multiple calls. -/
meta def normalize' (atoms : ref (buffer expr))
  (red : transparency) (mode := normalize_mode.horner) (e : expr) : tactic (expr × expr) :=
do
  pow_lemma ← simp_lemmas.mk.add_simp ``pow_one,
  let lemmas := match mode with
  | normalize_mode.SOP :=
    [``horner_def', ``add_zero, ``mul_one, ``mul_add, ``mul_sub,
    ``mul_assoc_rev, ``pow_add_rev, ``pow_add_rev_right,
    ``mul_neg, ``add_neg_eq_sub]
  | normalize_mode.horner :=
    [``horner.equations._eqn_1, ``add_zero, ``one_mul, ``pow_one,
    ``neg_mul, ``add_neg_eq_sub]
  | _ := []
  end,
  lemmas ← lemmas.mfoldl simp_lemmas.add_simp simp_lemmas.mk,
  trans_conv
    (λ e, do
      guard (mode ≠ normalize_mode.raw),
      (e', pr, _) ← simplify simp_lemmas.mk [] e,
      pure (e', pr))
    (λ e, do
      a ← read_ref atoms,
      (a, e', pr) ← ext_simplify_core a {}
        simp_lemmas.mk (λ _, failed) (λ a _ _ _ e, do
          write_ref atoms a,
          (new_e, pr) ← match mode with
          | normalize_mode.raw := eval' red atoms
          | normalize_mode.horner := trans_conv (eval' red atoms)
                                      (λ e, do (e', prf, _) ← simplify lemmas [] e, pure (e', prf))
          | normalize_mode.SOP :=
            trans_conv (eval' red atoms) $
            trans_conv (λ e, do (e', prf, _) ← simplify lemmas [] e, pure (e', prf)) $
            simp_bottom_up' (λ e, norm_num.derive e <|> pow_lemma.rewrite e)
          end e,
          guard (¬ new_e =ₐ e),
          a ← read_ref atoms,
          pure (a, new_e, some pr, ff))
        (λ _ _ _ _ _, failed) `eq e,
      write_ref atoms a,
      pure (e', pr))
    e




