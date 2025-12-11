import { test, expect } from '@playwright/test';

test('has title', async ({ page }) => {
  await page.goto('http://localhost:3000/?enable-coi');

  // Expect a title "to contain" a substring.
  await expect(page).toHaveTitle(/VS Code/);
});

test('can open tutorial', async ({ page }) => {
  await page.goto('http://localhost:3000/?enable-coi');

  await page.keyboard.press('Control+Shift+P');
  await page.keyboard.type('Waterproof: Open Tutorial');
  await page.keyboard.press('Enter');

  await expect(page).toHaveTitle(/VS Code/);
  await expect(page.getByText("inspecting the examples")).toBeVisible();
});


test('can open tactics', async ({ page }) => {
  await page.goto('http://localhost:3000/?enable-coi');

  const waterproofButton = page.getByRole('button', { name: 'Waterproof' });

  // await expect(waterproofButton).toBeVisible();
  await waterproofButton.click();

  await expect(page.getByText("Tactics")).toBeVisible();
});
