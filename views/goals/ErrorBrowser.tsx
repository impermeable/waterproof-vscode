import { PpString } from "../../lib/types";
import { RocqPp } from "../goals/RocqPp";
import React from "react";

//error PpString type
export type ErrorBrowserParams = { error: PpString };

//component to display the errors
export function ErrorBrowser({ error }: ErrorBrowserParams) {
  return (
    <>
      <header>Errors:</header>
      <RocqPp content={error} inline={true} />
    </>
  );
}
