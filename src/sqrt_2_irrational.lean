import data.nat.gcd
import data.real.irrational

lemma even_of_even_sqr {m : ℕ} (h : 2 ∣ m^2) : 2 ∣ m :=
begin
  rw [pow_two, nat.prime_two.dvd_mul] at h,
  cases h; assumption
end

example {m n : ℕ} (coprime_mn : m.coprime n) : m^2 ≠ 2 * n^2 :=
begin
  intro sqr_eq,
  have : 2 ∣ m,
  { apply even_of_even_sqr,
    rw sqr_eq,
    apply dvd_mul_right },
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this,
  have : 2 * (2 * k^2) = 2 * n^2,
  { rw [←sqr_eq, meq], ring },
  have : 2 * k^2 = n^2,
    from (mul_right_inj' (by norm_num)).mp this,
  have : 2 ∣ n,
  { apply even_of_even_sqr,
    rw ←this,
    apply dvd_mul_right },
  have : 2 ∣ m.gcd n,
    by apply nat.dvd_gcd; assumption,
  have : 2 ∣ 1,
  { convert this, symmetry, exact coprime_mn },
  norm_num at this
end