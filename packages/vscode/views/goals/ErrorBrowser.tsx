import { PpString } from "../../lib/types";
import { CoqPp } from "../goals/CoqPp";
import React from "react";

//error PpString type
export type ErrorBrowserParams = { error: PpString };

//component to display the errors
export function ErrorBrowser({ error }: ErrorBrowserParams) {
  return (
    <>
      <header>Errors:</header>
      <CoqPp content={error} inline={true} />;
    </>
  );
}
