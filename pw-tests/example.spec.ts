import { test, expect } from '@playwright/test';

test('has title', async ({ page }) => {
  await page.goto('http://localhost:3000/?enable-coi');

  // Expect a title "to contain" a substring.
  await expect(page).toHaveTitle(/VS Code/);
});

test('can open tactics', async ({ page }) => {
  await page.goto('http://localhost:3000/?enable-coi');

  const waterproofButton = page.getByRole('button', { name: 'Waterproof' });

  // await expect(waterproofButton).toBeVisible();
  await waterproofButton.click();

  await expect(page.getByText("Tactics")).toBeVisible();
});
