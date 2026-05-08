  // ── Theme toggle ──
  const root = document.documentElement;
  const btn = document.getElementById('theme-toggle');
  const emoji = document.getElementById('toggle-emoji');
  const label = document.getElementById('toggle-label');

  // Restore saved preference
  const saved = localStorage.getItem('sol-theme');
  if (saved === 'light') {
    root.setAttribute('data-theme', 'light');
    emoji.textContent = '🌙';
    label.textContent = 'Dark';
  }

  btn.addEventListener('click', () => {
    const isLight = root.getAttribute('data-theme') === 'light';
    if (isLight) {
      root.removeAttribute('data-theme');
      emoji.textContent = '☀️';
      label.textContent = 'Light';
      localStorage.setItem('sol-theme', 'dark');
    } else {
      root.setAttribute('data-theme', 'light');
      emoji.textContent = '🌙';
      label.textContent = 'Dark';
      localStorage.setItem('sol-theme', 'light');
    }
  });

  // ── Active nav link on scroll ──
  const sections = document.querySelectorAll('section[id]');
  const navLinks = document.querySelectorAll('nav#sidebar a');

  const observer = new IntersectionObserver((entries) => {
    entries.forEach(entry => {
      if (entry.isIntersecting) {
        navLinks.forEach(a => a.classList.remove('active'));
        const active = document.querySelector(`nav#sidebar a[href="#${entry.target.id}"]`);
        if (active) active.classList.add('active');
      }
    });
  }, { rootMargin: '-20% 0px -70% 0px' });

  sections.forEach(s => observer.observe(s));